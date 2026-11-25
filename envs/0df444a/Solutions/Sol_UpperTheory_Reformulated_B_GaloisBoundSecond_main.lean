-- Prove2me | solution 1 for UpperTheory.Reformulated.B.GaloisBoundSecond.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:02:31.003116+00:00
-- url     : https://prove2.me/submissions/2029175a-c80c-4ff4-9f3a-ceb39a33f3eb

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GaloisBoundSecond
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField
private lemma norm_le_prod {F : Type} [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (I : Ideal (RingOfIntegers F)) (y : RingOfIntegers F) (hy : y ∈ I) (h0 : y ≠ 0) :
    (Ideal.absNorm I : ℝ) ≤ ∏ w : InfinitePlace F, w (y : F) := by
  have hdvd : Ideal.absNorm I ∣ Ideal.absNorm (Ideal.span {y}) :=
    Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem I).2 hy)
  rw [Ideal.absNorm_span_singleton] at hdvd
  have hpos : 0 < (Algebra.norm ℤ y).natAbs := by
    rw [Int.natAbs_pos]
    exact (Algebra.norm_ne_zero_iff).2 h0
  have hle := Nat.le_of_dvd hpos hdvd
  have hprod : ∏ w : InfinitePlace F, w (y : F) = ((|Algebra.norm ℚ (y : F)| : ℚ) : ℝ) := by
    rw [← InfinitePlace.prod_eq_abs_norm]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [(NumberField.IsTotallyReal.isReal w).mult_eq_one, pow_one]
  rw [hprod, ← Algebra.coe_norm_int]
  have : ((Algebra.norm ℤ y).natAbs : ℝ) = |((Algebra.norm ℤ y : ℤ) : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have h2 : (Ideal.absNorm I : ℝ) ≤ ((Algebra.norm ℤ y).natAbs : ℝ) := by exact_mod_cast hle
  rw [this] at h2
  push_cast
  exact h2
private lemma sep {F : Type} [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (N : ℕ) (hN : 0 < N) (I : Ideal (RingOfIntegers F)) (x x' : F)
    (hx : ∃ y ∈ I, (y : F) = (N : F) * x) (hx' : ∃ y ∈ I, (y : F) = (N : F) * x') (hne : x ≠ x') :
    (Ideal.absNorm I : ℝ) ≤ ∏ w : InfinitePlace F, w ((N : F) * (x - x')) := by
  obtain ⟨y, hy, hyx⟩ := hx
  obtain ⟨y', hy', hyx'⟩ := hx'
  have hN' : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  have hcoe : ((y - y' : RingOfIntegers F) : F) = (N : F) * (x - x') := by
    have e : ((y - y' : RingOfIntegers F) : F) = (y : F) - (y' : F) := map_sub _ _ _
    rw [e, hyx, hyx']
    ring
  have h0 : y - y' ≠ 0 := by
    intro h
    rw [h] at hcoe
    have : (N : F) * (x - x') = 0 := by simpa using hcoe.symm
    rcases mul_eq_zero.1 this with h1 | h1
    · exact hN' h1
    · exact hne (sub_eq_zero.1 h1)
  have := norm_le_prod I (y - y') (I.sub_mem hy hy') h0
  rwa [hcoe] at this
private lemma key {F : Type} [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (N : ℕ) (hN : 0 < N) (I : Ideal (RingOfIntegers F)) (hI : I ≠ ⊥) (B : ℝ) (hB : 0 ≤ B)
    (S : Set F)
    (hS : S = {x : F | x ≠ 0 ∧ (∃ y ∈ I, (y : F) = (N : F) * x) ∧
      ∀ w : InfinitePlace F, (w : F → ℝ) x ≤ B}) :
    S.Finite ∧ (S.ncard : ℝ) * (Ideal.absNorm I : ℝ) ≤ (4 * B * N) ^ Module.finrank ℚ F := by
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rcases S.eq_empty_or_nonempty with hE | ⟨x0, hx0⟩
  · subst hE
    refine ⟨Set.finite_empty, ?_⟩
    simp only [Set.ncard_empty, Nat.cast_zero, zero_mul]
    positivity
  have hmem : ∀ x, x ∈ S → x ≠ 0 ∧ (∃ y ∈ I, (y : F) = (N : F) * x) ∧
      ∀ w : InfinitePlace F, (w : F → ℝ) x ≤ B := fun x hx => by
    rw [hS] at hx; exact hx
  set n := Module.finrank ℚ F with hn_def
  have hn : 0 < n := Module.finrank_pos
  have hcard : Fintype.card (InfinitePlace F) = n := by
    rw [hn_def, ← InfinitePlace.sum_mult_eq, Finset.card_univ.symm, Finset.card_eq_sum_ones]
    exact Finset.sum_congr rfl fun w _ => ((NumberField.IsTotallyReal.isReal w).mult_eq_one).symm
  set C : ℝ := B * N with hC
  have hC0 : 0 ≤ C := by positivity
  set A : ℝ := (Ideal.absNorm I : ℝ) with hA
  have hA0 : 0 < A := by
    have : Ideal.absNorm I ≠ 0 := fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)
    rw [hA]; exact_mod_cast Nat.pos_of_ne_zero this
  set s : ℝ := A ^ ((n : ℝ)⁻¹) with hs_def
  have hs : s ^ n = A := Real.rpow_inv_natCast_pow hA0.le hn.ne'
  have hs0 : 0 < s := Real.rpow_pos_of_pos hA0 _
  have hN'F : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  have hwN : ∀ (w : InfinitePlace F) (z : F), w ((N : F) * z) = N * w z := by
    intro w z
    rw [map_mul]
    congr 1
    have := w.norm_embedding_eq (N : F)
    rw [← this]
    simp
  have hAC : A ≤ C ^ n := by
    have h1 := sep N hN I x0 0 (hmem x0 hx0).2.1 ⟨0, I.zero_mem, by simp⟩ (hmem x0 hx0).1
    refine h1.trans ?_
    rw [← hcard, ← Finset.card_univ, ← Finset.prod_const]
    refine Finset.prod_le_prod (fun w _ => w.1.nonneg _) fun w _ => ?_
    rw [sub_zero, hwN, hC, mul_comm]
    exact mul_le_mul_of_nonneg_right ((hmem x0 hx0).2.2 w) hNr.le
  have hsC : s ≤ C := by
    have : s ^ n ≤ C ^ n := by rw [hs]; exact hAC
    exact (pow_le_pow_iff_left₀ hs0.le hC0 hn.ne').1 this
  let ρ : InfinitePlace F → (F →+* ℝ) := fun w =>
    InfinitePlace.embedding_of_isReal (NumberField.IsTotallyReal.isReal w)
  have hρ : ∀ w z, |ρ w z| = w z := fun w z => by
    simpa [Real.norm_eq_abs] using
      InfinitePlace.norm_embedding_of_isReal (NumberField.IsTotallyReal.isReal w) z
  set K : ℤ := ⌊2 * C / s⌋ with hK
  let f : F → InfinitePlace F → ℤ := fun x w => ⌊((N : ℝ) * ρ w x + C) / s⌋
  let T : Finset (InfinitePlace F → ℤ) := Fintype.piFinset fun _ => Finset.Icc 0 K
  have hmaps : ∀ x ∈ S, f x ∈ (T : Set (InfinitePlace F → ℤ)) := by
    intro x hx
    simp only [T, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
    intro w
    have hb : |ρ w x| ≤ B := by rw [hρ]; exact (hmem x hx).2.2 w
    obtain ⟨hb1, hb2⟩ := abs_le.1 hb
    have h1 : -C ≤ (N : ℝ) * ρ w x := by
      have := mul_le_mul_of_nonneg_left hb1 hNr.le
      rw [hC]; linarith
    have h2 : (N : ℝ) * ρ w x ≤ C := by
      have := mul_le_mul_of_nonneg_left hb2 hNr.le
      rw [hC]; linarith
    constructor
    · exact Int.floor_nonneg.2 (div_nonneg (by linarith) hs0.le)
    · exact Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hs0.le)
  have hinj : Set.InjOn f S := by
    intro x hx x' hx' hff
    by_contra hne
    have h1 := sep N hN I x x' (hmem x hx).2.1 (hmem x' hx').2.1 hne
    have hz : (N : F) * (x - x') ≠ 0 := mul_ne_zero hN'F (sub_ne_zero.2 hne)
    have h2 : ∏ w : InfinitePlace F, w ((N : F) * (x - x')) < ∏ _w : InfinitePlace F, s := by
      refine Finset.prod_lt_prod_of_nonempty (fun w _ => w.pos_iff.2 hz) (fun w _ => ?_)
        Finset.univ_nonempty
      have hw := congrFun hff w
      have h3 := Int.abs_sub_lt_one_of_floor_eq_floor hw
      rw [← sub_div, abs_div, abs_of_pos hs0, div_lt_one hs0] at h3
      have h4 : w ((N : F) * (x - x')) = |(N : ℝ) * ρ w x + C - ((N : ℝ) * ρ w x' + C)| := by
        rw [hwN, ← hρ w (x - x'), map_sub, ← abs_of_pos hNr, ← abs_mul, abs_of_pos hNr]
        congr 1
        ring
      rw [h4]
      exact h3
    rw [Finset.prod_const, Finset.card_univ, hcard, hs] at h2
    linarith
  have hTfin : (T : Set (InfinitePlace F → ℤ)).Finite := T.finite_toSet
  refine ⟨Set.Finite.of_injOn (f := f) hmaps hinj hTfin, ?_⟩
  have hle := Set.ncard_le_ncard_of_injOn f hmaps hinj hTfin
  have hK0 : 0 ≤ K := Int.floor_nonneg.2 (by positivity)
  have hTc : (T : Set (InfinitePlace F → ℤ)).ncard = (K.toNat + 1) ^ n := by
    rw [Set.ncard_coe_finset]
    simp only [T, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ, hcard]
    congr 1
    omega
  rw [hTc] at hle
  have hle' : (S.ncard : ℝ) ≤ ((K : ℝ) + 1) ^ n := by
    have : (S.ncard : ℝ) ≤ (((K.toNat + 1) ^ n : ℕ) : ℝ) := by exact_mod_cast hle
    refine this.trans (le_of_eq ?_)
    push_cast
    congr 2
    exact_mod_cast Int.toNat_of_nonneg hK0
  have hKs : ((K : ℝ) + 1) * s ≤ 4 * C := by
    have h1 : (K : ℝ) ≤ 2 * C / s := Int.floor_le _
    have h2 : (K : ℝ) * s ≤ 2 * C := (le_div_iff₀ hs0).1 h1
    nlinarith
  have hK1 : (0 : ℝ) ≤ (K : ℝ) + 1 := by
    have : (0 : ℝ) ≤ K := by exact_mod_cast hK0
    linarith
  calc (S.ncard : ℝ) * A ≤ ((K : ℝ) + 1) ^ n * s ^ n := by
        rw [hs]; exact mul_le_mul_of_nonneg_right hle' hA0.le
    _ = (((K : ℝ) + 1) * s) ^ n := (mul_pow _ _ _).symm
    _ ≤ (4 * C) ^ n := pow_le_pow_left₀ (by positivity) hKs n
    _ = (4 * B * N) ^ n := by rw [hC]; ring_nf
end

set_option autoImplicit false
open NumberField
namespace UpperTheory.Reformulated.B.GaloisBoundSecond
theorem _root_.solution :
    ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F] [NumberField.IsTotallyReal F] (N : ℕ),
      (0 : ℕ) < N →
        ∀ (I : Ideal (NumberField.RingOfIntegers F)),
          I ≠ ⊥ →
            ∀ (B : ℝ),
              (0 : ℝ) ≤ B →
                {x : F |
                      x ≠ (0 : F) ∧
                        (∃ y ∈ I, (↑y : F) = (↑N : F) * x) ∧
                          ∀ (w : NumberField.InfinitePlace F), (w : F → ℝ) x ≤ B}.Finite ∧
                  (↑{x : F |
                              x ≠ (0 : F) ∧
                                (∃ y ∈ I, (↑y : F) = (↑N : F) * x) ∧
                                  ∀ (w : NumberField.InfinitePlace F), (w : F → ℝ) x ≤ B}.ncard :
                        ℝ) *
                      (↑((Ideal.absNorm : Ideal (NumberField.RingOfIntegers F) → ℕ) I) : ℝ) ≤
                    ((4 : ℝ) * B * (↑N : ℝ)) ^ Module.finrank ℚ F := by
  intro F _ _ _ N hN I hI B hB
  exact key N hN I hI B hB _ rfl
end UpperTheory.Reformulated.B.GaloisBoundSecond
