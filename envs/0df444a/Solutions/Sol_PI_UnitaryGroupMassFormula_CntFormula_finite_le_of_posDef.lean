-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CntFormula.finite_le_of_posDef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:38:02.528203+00:00
-- url     : https://prove2.me/submissions/a724a652-2d7a-4702-8327-0f7cc1508d4b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_FiniteLeOfPosDef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CntFormula
namespace PI.UnitaryGroupMassFormula.CntFormula
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (B : LinearMap.BilinForm ℚ V) (hS : ∀ x y, B x y = B y x) (hpos : ∀ v, v ≠ 0 → 0 < B v v)
    (A : Submodule ℤ V) (hA : A.FG) (c : ℚ) : {v | v ∈ A ∧ B v v ≤ c}.Finite := by
  classical
  obtain ⟨S, hS'⟩ := hA
  have hnn : ∀ v, 0 ≤ B v v := fun v => by
    by_cases hv : v = 0
    · simp [hv]
    · exact (hpos v hv).le

  have cs : ∀ v w, B v w ^ 2 ≤ B v v * B w w := by
    intro v w
    by_cases hw : w = 0
    · simp [hw]
    · have hww := hpos w hw
      have key := hnn (B w w • v - B v w • w)
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
        hS w v] at key
      have h2 : B w w * B v w ^ 2 ≤ B w w * (B v v * B w w) := by nlinarith [key]
      exact le_of_mul_le_mul_left h2 hww
  let b := Module.finBasis ℚ V
  have hinj : ∀ v w, (∀ i, B v (b i) = B w (b i)) → v = w := by
    intro v w h
    have h0 : B (v - w) = 0 := b.ext fun i => by simp [map_sub, h i]
    by_contra hne
    have h1 := hpos (v - w) (sub_ne_zero.2 hne)
    rw [h0] at h1
    simp at h1
  let N : ℕ := ∏ s ∈ S, ∏ i, (B s (b i)).den
  have hNpos : 0 < N :=
    Finset.prod_pos fun s _ => Finset.prod_pos fun i _ => Nat.pos_of_ne_zero (Rat.den_nz _)

  have hint : ∀ v ∈ A, ∀ i, ∃ z : ℤ, (z : ℚ) = N * B v (b i) := by
    intro v hv
    rw [← hS'] at hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      intro i
      have hd : (B x (b i)).den ∣ N :=
        (Finset.dvd_prod_of_mem (fun i => (B x (b i)).den) (Finset.mem_univ i)).trans
          (Finset.dvd_prod_of_mem (fun s => ∏ i, (B s (b i)).den) hx)
      obtain ⟨k, hk⟩ := hd
      refine ⟨k * (B x (b i)).num, ?_⟩
      have e := Rat.mul_den_eq_num (B x (b i))
      rw [hk]
      push_cast
      linear_combination (-(k : ℚ)) * e
    | zero => intro i; exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      intro i
      obtain ⟨z1, h1⟩ := hx i
      obtain ⟨z2, h2⟩ := hy i
      refine ⟨z1 + z2, ?_⟩
      rw [map_add, LinearMap.add_apply]
      push_cast
      rw [h1, h2]
      ring
    | smul a x _ hx =>
      intro i
      obtain ⟨z, hz⟩ := hx i
      refine ⟨a * z, ?_⟩
      rw [← Int.cast_smul_eq_zsmul ℚ a x, map_smul, LinearMap.smul_apply, smul_eq_mul]
      push_cast
      rw [hz]
      ring
  have hbd : ∀ v, B v v ≤ c → ∀ i, |B v (b i)| ≤ 1 + |c| * B (b i) (b i) := by
    intro v hv i
    have h1 := cs v (b i)
    have h2 : B v v * B (b i) (b i) ≤ |c| * B (b i) (b i) :=
      mul_le_mul_of_nonneg_right (hv.trans (le_abs_self c)) (hnn _)
    have h3 : |B v (b i)| ≤ 1 + B v (b i) ^ 2 := by
      nlinarith [sq_nonneg (|B v (b i)| - 1), sq_abs (B v (b i))]
    linarith
  let g : V → Fin (Module.finrank ℚ V) → ℤ := fun v i => round ((N : ℚ) * B v (b i))
  have hg : ∀ v ∈ A, ∀ i, ((g v i : ℤ) : ℚ) = N * B v (b i) := by
    intro v hv i
    obtain ⟨z, hz⟩ := hint v hv i
    simp only [g]
    rw [← hz, round_intCast]
  apply Set.Finite.of_finite_image (f := g)
  · refine Set.Finite.subset (Set.Finite.pi (t := fun i =>
      Set.Icc (-⌈(N : ℚ) * (1 + |c| * B (b i) (b i))⌉) ⌈(N : ℚ) * (1 + |c| * B (b i) (b i))⌉)
      fun i => Set.finite_Icc _ _) ?_
    rintro _ ⟨v, ⟨hvA, hvc⟩, rfl⟩
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
    intro i
    have e := hg v hvA i
    have hb : |((g v i : ℤ) : ℚ)| ≤ N * (1 + |c| * B (b i) (b i)) := by
      rw [e, abs_mul, Nat.abs_cast]
      exact mul_le_mul_of_nonneg_left (hbd v hvc i) (Nat.cast_nonneg _)
    have hK := Int.le_ceil ((N : ℚ) * (1 + |c| * B (b i) (b i)))
    have l1 := neg_abs_le ((g v i : ℤ) : ℚ)
    have l2 := le_abs_self ((g v i : ℤ) : ℚ)
    constructor
    · have : ((-⌈(N : ℚ) * (1 + |c| * B (b i) (b i))⌉ : ℤ) : ℚ) ≤ ((g v i : ℤ) : ℚ) := by
        push_cast
        linarith
      exact_mod_cast this
    · have : ((g v i : ℤ) : ℚ) ≤ ((⌈(N : ℚ) * (1 + |c| * B (b i) (b i))⌉ : ℤ) : ℚ) := by
        linarith
      exact_mod_cast this
  · rintro v ⟨hvA, -⟩ w ⟨hwA, -⟩ hvw
    apply hinj
    intro i
    have e : (N : ℚ) * B v (b i) = N * B w (b i) := by
      rw [← hg v hvA i, ← hg w hwA i, congrFun hvw i]
    exact mul_left_cancel₀ (by exact_mod_cast hNpos.ne') e
end PI.UnitaryGroupMassFormula.CntFormula
