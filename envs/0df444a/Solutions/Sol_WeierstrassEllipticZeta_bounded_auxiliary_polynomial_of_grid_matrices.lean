-- Prove2me | solution 1 for WeierstrassEllipticZeta.bounded_auxiliary_polynomial_of_grid_matrices
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-14T00:28:04.06474+00:00
-- url     : https://prove2.me/submissions/4edde820-c586-42d9-9947-63b3fe0ad902

import Mathlib.NumberTheory.SiegelsLemma
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_WeierstrassEllipticZeta_GridJetMatrices
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Tactic.FinCases

open Polynomial Matrix Finset
open scoped Polynomial

noncomputable section

namespace TranscendenceTheory.BivariateSiegel

def ofBox (D E : ℕ) (v : Fin (E + 1) × Fin (D + 1) → ℤ) : ℤ[X][X] :=
  ofFn (E + 1) fun j => ofFn (D + 1) fun k => v (j, k)

lemma ofBox_coeff (D E : ℕ) (v : Fin (E + 1) × Fin (D + 1) → ℤ)
    (j : Fin (E + 1)) (k : Fin (D + 1)) :
    ((ofBox D E v).coeff j).coeff k = v (j, k) := by
  rw [ofBox, ofFn_coeff_eq_val_of_lt _ j.isLt, ofFn_coeff_eq_val_of_lt _ k.isLt]

lemma ofBox_degree (D E : ℕ) (v : Fin (E + 1) × Fin (D + 1) → ℤ) :
    (ofBox D E v).natDegree ≤ E ∧ ∀ j, ((ofBox D E v).coeff j).natDegree ≤ D := by
  refine ⟨Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) _), ?_⟩
  intro j
  by_cases hj : j < E + 1
  · simp only [ofBox, ofFn_coeff_eq_val_of_lt _ hj]
    exact Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) _)
  · simp [ofBox, ofFn_coeff_eq_zero_of_ge _ (by omega : E + 1 ≤ j)]

lemma ofBox_eq_sum (D E : ℕ) (v : Fin (E + 1) × Fin (D + 1) → ℤ) :
    ofBox D E v = ∑ j : Fin (E + 1), ∑ k : Fin (D + 1),
      monomial j (monomial k (v (j, k))) := by
  simp only [ofBox, ofFn_eq_sum_monomial, map_sum]

lemma inner_degree_mul (p q : ℤ[X][X]) (D D' : ℕ)
    (hp : ∀ j, (p.coeff j).natDegree ≤ D)
    (hq : ∀ j, (q.coeff j).natDegree ≤ D') :
    ∀ j, ((p * q).coeff j).natDegree ≤ D + D' := by
  intro j
  rw [coeff_mul]
  exact natDegree_sum_le_of_forall_le _ _ fun a _ =>
    (natDegree_mul_le).trans (Nat.add_le_add (hp a.1) (hq a.2))

lemma inner_degree_sum {ι : Type*} (s : Finset ι) (p : ι → ℤ[X][X]) (D : ℕ)
    (hp : ∀ i ∈ s, ∀ j, ((p i).coeff j).natDegree ≤ D) :
    ∀ j, ((∑ i ∈ s, p i).coeff j).natDegree ≤ D := by
  intro j
  rw [finsetSum_coeff]
  exact natDegree_sum_le_of_forall_le _ _ fun i hi => hp i hi j

lemma coeff_mul_monomial' (p : ℤ[X]) (j k : ℕ) (a : ℤ) :
    (p * monomial j a).coeff k = if j ≤ k then p.coeff (k - j) * a else 0 := by
  rw [← C_mul_X_pow_eq_monomial, ← mul_assoc, coeff_mul_X_pow', coeff_mul_C]

lemma double_coeff_mul_monomial (p : ℤ[X][X]) (j k a b : ℕ) (v : ℤ) :
    ((p * monomial a (monomial b v)).coeff j).coeff k =
      (if a ≤ j ∧ b ≤ k then (p.coeff (j - a)).coeff (k - b) else 0) * v := by
  rw [← C_mul_X_pow_eq_monomial, ← mul_assoc, coeff_mul_X_pow']
  by_cases ha : a ≤ j
  · simp only [if_pos ha, coeff_mul_C]
    rw [coeff_mul_monomial']
    split <;> simp_all
  · simp [ha]

attribute [local instance] Matrix.seminormedAddCommGroup

lemma integer_kernel {α β : Type*} [Fintype α] [Fintype β]
    (B : Matrix α β ℤ) (hn : 0 < Fintype.card β)
    (hdim : 2 * Fintype.card α ≤ Fintype.card β)
    (H : ℝ) (hH : 1 ≤ H) (hB : ∀ i j, ‖B i j‖ ≤ H) :
    ∃ v : β → ℤ, v ≠ 0 ∧ B *ᵥ v = 0 ∧ ∀ j, ‖v j‖ ≤ Fintype.card β * H := by
  classical
  have hβ : (1 : ℝ) ≤ Fintype.card β := by exact_mod_cast hn
  have hbound : 1 ≤ (Fintype.card β : ℝ) * H := one_le_mul_of_one_le_of_one_le hβ hH
  by_cases hm : Fintype.card α = 0
  · have : IsEmpty α := Fintype.card_eq_zero_iff.mp hm
    obtain ⟨j⟩ := Fintype.card_pos_iff.mp hn
    refine ⟨fun _ => 1, ?_, by ext i; exact isEmptyElim i, ?_⟩
    · intro h
      have := congrFun h j
      norm_num at this
    · intro j
      simpa using hbound
  · have hmn : Fintype.card α < Fintype.card β := by omega
    have he0 : 0 ≤ (Fintype.card α : ℝ) / (Fintype.card β - Fintype.card α) := by
      apply div_nonneg (Nat.cast_nonneg _)
      exact sub_nonneg.mpr (by exact_mod_cast hmn.le)
    have he1 : (Fintype.card α : ℝ) / (Fintype.card β - Fintype.card α) ≤ 1 := by
      apply (div_le_one (sub_pos.mpr (by exact_mod_cast hmn))).mpr
      have : (2 : ℝ) * Fintype.card α ≤ Fintype.card β := by exact_mod_cast hdim
      linarith
    obtain ⟨v, hv, hvB, hvnorm⟩ := Int.Matrix.exists_ne_zero_int_vec_norm_le B hmn (by omega)
    refine ⟨v, hv, hvB, fun j => (norm_le_pi_norm v j).trans (hvnorm.trans ?_)⟩
    have hmax : max 1 ‖B‖ ≤ H := max_le hH ((Matrix.norm_le_iff (by linarith)).mpr hB)
    exact (Real.rpow_le_rpow (by positivity)
      (mul_le_mul_of_nonneg_left hmax (Nat.cast_nonneg _)) he0).trans
      (Real.rpow_le_self_of_one_le hbound he1)

theorem bivariate_siegel (m n D E : ℕ) (hn : 0 < n) (hdim : 8 * m ≤ n)
    (B : Matrix (Fin m) (Fin n) ℤ[X][X]) (H : ℝ) (hH : 1 ≤ H)
    (hBy : ∀ r i, (B r i).natDegree ≤ E)
    (hBx : ∀ r i j, ((B r i).coeff j).natDegree ≤ D)
    (hBH : ∀ r i j k, ‖((B r i).coeff j).coeff k‖ ≤ H) :
    ∃ p : Fin n → ℤ[X][X], p ≠ 0 ∧
      (∀ r, ∑ i, B r i * p i = 0) ∧
      (∀ i, (p i).natDegree ≤ E) ∧
      (∀ i j, ((p i).coeff j).natDegree ≤ D) ∧
      ∀ i j k, ‖((p i).coeff j).coeff k‖ ≤ (n : ℝ) * (E + 1) * (D + 1) * H := by
  classical
  let α := Fin m × Fin (2 * E + 1) × Fin (2 * D + 1)
  let β := Fin n × Fin (E + 1) × Fin (D + 1)
  let M : Matrix α β ℤ := fun r i =>
    if i.2.1.val ≤ r.2.1.val ∧ i.2.2.val ≤ r.2.2.val then
      ((B r.1 i.1).coeff (r.2.1.val - i.2.1.val)).coeff (r.2.2.val - i.2.2.val)
    else 0
  have hcardα : Fintype.card α = m * ((2 * E + 1) * (2 * D + 1)) := by simp [α]
  have hcardβ : Fintype.card β = n * ((E + 1) * (D + 1)) := by simp [β]
  have hcard : 2 * Fintype.card α ≤ Fintype.card β := by
    rw [hcardα, hcardβ]
    calc
      _ ≤ (8 * m) * ((E + 1) * (D + 1)) := by nlinarith [Nat.zero_le (m * E), Nat.zero_le (m * D)]
      _ ≤ _ := Nat.mul_le_mul_right _ hdim
  obtain ⟨v, hv, hvM, hvH⟩ := integer_kernel M
    (by rw [hcardβ]; positivity) hcard H hH (fun r i => by
      dsimp [M]
      split
      · exact hBH _ _ _ _
      · simpa using (show 0 ≤ H by linarith))
  let p : Fin n → ℤ[X][X] := fun i => ofBox D E (fun jk => v (i, jk))
  have hpdeg : ∀ i, (p i).natDegree ≤ E ∧ ∀ j, ((p i).coeff j).natDegree ≤ D :=
    fun i => ofBox_degree D E (fun jk => v (i, jk))
  refine ⟨p, ?_, ?_, fun i => (hpdeg i).1, fun i => (hpdeg i).2, ?_⟩
  · intro hp
    apply hv
    funext ⟨i, j, k⟩
    have he := congrArg (fun q : ℤ[X][X] => (q.coeff j).coeff k) (congrFun hp i)
    simpa only [p, ofBox_coeff, Pi.zero_apply, coeff_zero] using he
  · intro r
    have hy : (∑ i, B r i * p i).natDegree ≤ 2 * E :=
      natDegree_sum_le_of_forall_le _ _ fun i _ =>
        (natDegree_mul_le).trans (by have := hBy r i; have := (hpdeg i).1; omega)
    have hx : ∀ j, ((∑ i, B r i * p i).coeff j).natDegree ≤ 2 * D := by
      apply inner_degree_sum
      intro i _
      simpa [two_mul] using inner_degree_mul (B r i) (p i) D D (hBx r i) (hpdeg i).2
    apply Polynomial.ext
    intro j
    by_cases hj : j < 2 * E + 1
    · apply Polynomial.ext
      intro k
      by_cases hk : k < 2 * D + 1
      · have he := congrFun hvM (r, ⟨j, hj⟩, ⟨k, hk⟩)
        simpa only [Matrix.mulVec, dotProduct, β, Fintype.sum_prod_type,
          p, ofBox_eq_sum, Finset.mul_sum, finsetSum_coeff, double_coeff_mul_monomial,
          M, Pi.zero_apply, coeff_zero] using he
      · simp only [coeff_zero]
        exact coeff_eq_zero_of_natDegree_lt ((hx j).trans_lt (by omega))
    · simp only [coeff_zero]
      exact coeff_eq_zero_of_natDegree_lt (hy.trans_lt (by omega))
  · intro i j k
    by_cases hj : j < E + 1
    · by_cases hk : k < D + 1
      · have he := hvH (i, ⟨j, hj⟩, ⟨k, hk⟩)
        rw [hcardβ] at he
        simpa only [p, ofBox, ofFn_coeff_eq_val_of_lt _ hj,
          ofFn_coeff_eq_val_of_lt _ hk, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
          mul_assoc] using he
      · rw [coeff_eq_zero_of_natDegree_lt ((hpdeg i).2 j |>.trans_lt (by omega)), norm_zero]
        positivity
    · rw [coeff_eq_zero_of_natDegree_lt ((hpdeg i).1.trans_lt (by omega)), coeff_zero, norm_zero]
      positivity

end TranscendenceTheory.BivariateSiegel

open scoped Polynomial
open Filter WeierstrassEllipticZeta
noncomputable section
set_option maxHeartbeats 1000000

private theorem p2m_grid_mono (ω u₁ u₂ : ℂ) (A B : Fin 3 → ℕ) (hAB : ∀ i, A i ≤ B i) :
    auxiliaryGrid u₁ u₂ ω A ⊆ auxiliaryGrid u₁ u₂ ω B := by
  intro v hv
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hv
  refine Finset.mem_image.mpr ⟨fun i => (t i).castLE (hAB i), Finset.mem_univ _, ?_⟩
  rfl

private theorem p2m_bivariate_coeff_norm_le (p : ℤ[X][X]) (j k : ℕ) :
    ‖(p.coeff j).coeff k‖ ≤
      ((∑ a ∈ p.support, ∑ b ∈ (p.coeff a).support,
        ((p.coeff a).coeff b).natAbs) : ℝ) := by
  classical
  by_cases hj : j ∈ p.support
  · by_cases hk : k ∈ (p.coeff j).support
    · have h1 : ((p.coeff j).coeff k).natAbs ≤
          ∑ b ∈ (p.coeff j).support, ((p.coeff j).coeff b).natAbs :=
        Finset.single_le_sum (f := fun b => ((p.coeff j).coeff b).natAbs) (fun _ _ => Nat.zero_le _) hk
      have h2 : (∑ b ∈ (p.coeff j).support, ((p.coeff j).coeff b).natAbs) ≤
          ∑ a ∈ p.support, ∑ b ∈ (p.coeff a).support, ((p.coeff a).coeff b).natAbs :=
        Finset.single_le_sum (f := fun a => ∑ b ∈ (p.coeff a).support, ((p.coeff a).coeff b).natAbs) (fun _ _ => Nat.zero_le _) hj
      have h := h1.trans h2
      have hnorm : ‖(p.coeff j).coeff k‖ = (((p.coeff j).coeff k).natAbs : ℝ) := by
        simp only [Int.norm_eq_abs, ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
      rw [hnorm]
      exact_mod_cast h
    · rw [Polynomial.notMem_support_iff.mp hk, norm_zero]
      positivity
  · rw [Polynomial.notMem_support_iff.mp hj, Polynomial.coeff_zero, norm_zero]
    positivity

private theorem bounded_kernel {ρ ι : Type} [Fintype ρ] [Fintype ι]
    (θ ν : ℂ) (g : ℤ[X][X]) (hg : 0 < g.natDegree)
    (hker : ∀ p : ℤ[X][X],
      p.eval₂ (Polynomial.aeval θ).toRingHom ν = 0 ↔ g ∣ p)
    (D : ℕ) (H : ℝ) (hH : 1 ≤ H)
    (hn : 0 < Fintype.card ι) (hgap : 8 * Fintype.card ρ ≤ Fintype.card ι)
    (M : ρ → ι → ℤ[X][X])
    (hM : ∀ r i, (M r i).natDegree < g.natDegree ∧
      (∀ j, ((M r i).coeff j).natDegree ≤ D) ∧
      ∀ j k, ‖((M r i).coeff j).coeff k‖ ≤ H) :
    ∃ p : ι → ℤ[X][X],
      (fun i => (p i).eval₂ (Polynomial.aeval θ).toRingHom ν) ≠ 0 ∧
      (∀ r, ∑ i, (M r i).eval₂ (Polynomial.aeval θ).toRingHom ν *
        (p i).eval₂ (Polynomial.aeval θ).toRingHom ν = 0) ∧
      (∀ i, (p i).natDegree < g.natDegree) ∧
      (∀ i j, ((p i).coeff j).natDegree ≤ D) ∧
      ∀ i j k, ‖((p i).coeff j).coeff k‖ ≤
        (Fintype.card ι : ℝ) * g.natDegree * (D + 1) * H := by
  classical
  let eI := Fintype.equivFin ι
  let eR := Fintype.equivFin ρ
  obtain ⟨p, hp, hpM, hpy, hpx, hpH⟩ :=
    TranscendenceTheory.BivariateSiegel.bivariate_siegel
      (Fintype.card ρ) (Fintype.card ι) D (g.natDegree - 1) hn hgap
      (fun r i => M (eR.symm r) (eI.symm i)) H hH
      (fun r i => by have := (hM (eR.symm r) (eI.symm i)).1; omega)
      (fun r i => (hM _ _).2.1) (fun r i => (hM _ _).2.2)
  let q : ι → ℤ[X][X] := fun i => p (eI i)
  have hqy (i : ι) : (q i).natDegree < g.natDegree := by
    have := hpy (eI i)
    dsimp [q]
    omega
  refine ⟨q, ?_, ?_, hqy, fun i => hpx (eI i), ?_⟩
  · intro hz
    apply hp
    funext j
    have heval : (q (eI.symm j)).eval₂ (Polynomial.aeval θ).toRingHom ν = 0 :=
      congrFun hz (eI.symm j)
    have hzero := Polynomial.eq_zero_of_dvd_of_natDegree_lt
      ((hker _).mp heval) (hqy (eI.symm j))
    simpa only [q, eI.apply_symm_apply, Pi.zero_apply] using hzero
  · intro r
    have hsum : (∑ i, M r i * q i) = 0 := by
      calc
        _ = ∑ i, M r (eI.symm i) * p i :=
          Fintype.sum_equiv eI _ _ (fun i => by simp only [q, eI.symm_apply_apply])
        _ = 0 := by simpa only [eR.symm_apply_apply] using hpM (eR r)
    have heval := congrArg (fun p : ℤ[X][X] =>
      p.eval₂ (Polynomial.aeval θ).toRingHom ν) hsum
    simpa only [Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul,
      Polynomial.eval₂_zero] using heval
  · intro i j k
    have h := hpH (eI i) j k
    have he : ((g.natDegree - 1 : ℕ) : ℝ) + 1 = g.natDegree := by
      exact_mod_cast (Nat.sub_add_cancel hg)
    simpa only [q, he] using h

theorem solution
    (L : PeriodPair) (ω u₁ u₂ θ ν : ℂ) (g : ℤ[X][X]) (d : ℤ[X])
    (hg : 0 < g.natDegree)
    (hker : ∀ p : ℤ[X][X],
      p.eval₂ (Polynomial.aeval θ).toRingHom ν = 0 ↔ g ∣ p)
    (hmat : AuxiliaryGridJetMatrixData L ω u₁ u₂ θ ν g d) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in Filter.atTop,
      let m := auxiliaryL0 N
      let l := auxiliaryL N
      ∃ p : Fin (m + 1) × Fin (l + 1) × Fin (l + 1) → ℤ[X][X],
        (fun i => (p i).eval₂ (Polynomial.aeval θ).toRingHom ν) ≠ 0 ∧
        (∀ i, (p i).natDegree < g.natDegree) ∧
        (∀ i j, (((p i).coeff j).natDegree : ℝ) ≤ C * m) ∧
        (∀ i j k, ‖((p i).coeff j).coeff k‖ ≤ Real.exp (C * N)) ∧
        ∀ v ∈ auxiliaryGrid u₁ u₂ ω ![auxiliaryS N, auxiliaryS N, auxiliaryS3 N],
          ∀ n ≤ m, iteratedDeriv n (fun w => ∑ i,
            (p i).eval₂ (Polynomial.aeval θ).toRingHom ν * w ^ i.1.val *
              L.weierstrassP w ^ i.2.1.val * weierstrassZeta L w ^ i.2.2.val)
                (u₁ / 2 + v) = 0 := by
  classical
  obtain ⟨_, hmats⟩ := hmat
  obtain ⟨A, hA, hNs⟩ := hmats 1
  refine ⟨2 * A, by positivity, ?_⟩
  filter_upwards [hNs] with N hN
  dsimp only at hN ⊢
  simp_rw [one_mul] at hN
  let m := auxiliaryL0 N
  let l := auxiliaryL N
  let s := auxiliaryS N
  let q := auxiliaryS3 N
  let Γ := auxiliaryGrid u₁ u₂ ω ![s, s, q]
  let Γ₃ := auxiliaryGrid u₁ u₂ ω ![3 * s, 3 * s, 3 * q]
  let I := Fin (m + 1) × Fin (l + 1) × Fin (l + 1)
  obtain ⟨D, R, Q, hD, hsize, hgap, hR, _, _, hkernel⟩ := hN
  have hinc : Γ ⊆ Γ₃ := p2m_grid_mono ω u₁ u₂ _ _ (by
    intro i
    fin_cases i
    · change s ≤ 3 * s; omega
    · change s ≤ 3 * s; omega
    · change q ≤ 3 * q; omega)
  let lift : Γ → Γ₃ := fun v => ⟨v.val, hinc v.property⟩
  let M : (Γ × Fin (1 * m + 1)) → I → ℤ[X][X] := fun r i => R (lift r.1) r.2 i
  have hcardI : Fintype.card I = (m + 1) * (l + 1) ^ 2 := by
    simp [I, Fintype.card_prod, pow_two]
  have hcardR : Fintype.card (Γ × Fin (1 * m + 1)) = (m + 1) * Γ.card := by
    simp [Fintype.card_prod, mul_comm]
  obtain ⟨p, hp, hpM, hpy, hpx, hpH⟩ := bounded_kernel θ ν g hg hker D
    (Real.exp (A * N)) (Real.one_le_exp_iff.mpr (by positivity))
    (by rw [hcardI]; positivity) (by simpa only [hcardI, hcardR] using hgap) M (by
      intro r i
      refine ⟨(hR (lift r.1) r.2 i).1, (hR (lift r.1) r.2 i).2.1, ?_⟩
      intro j k
      exact (p2m_bivariate_coeff_norm_le _ j k).trans (hR (lift r.1) r.2 i).2.2)
  refine ⟨p, hp, hpy, ?_, ?_, ?_⟩
  · intro i j
    have h : (((p i).coeff j).natDegree : ℝ) ≤ D := by exact_mod_cast hpx i j
    exact h.trans (hD.trans (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)))
  · intro i j k
    apply (hpH i j k).trans
    have hsize' : (Fintype.card I : ℝ) * g.natDegree * (D + 1) ≤ Real.exp (A * N) := by
      calc
        _ ≤ (Fintype.card I : ℝ) * (g.natDegree + 1) * (D + 1) := by
          gcongr
          linarith
        _ ≤ _ := by
          simpa only [hcardI, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using hsize
    calc
      _ ≤ Real.exp (A * N) * Real.exp (A * N) :=
        mul_le_mul_of_nonneg_right hsize' (Real.exp_pos _).le
      _ = Real.exp (2 * A * N) := by rw [← Real.exp_add]; congr 1; ring
  · intro v hv n hn
    apply (hkernel (lift ⟨v, hv⟩) (fun i =>
      (p i).eval₂ (Polynomial.aeval θ).toRingHom ν)).mp
      (fun j => hpM (⟨v, hv⟩, j)) n
    simpa only [one_mul] using hn
