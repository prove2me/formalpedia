-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P70.lemma9_1_one_eigenline
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T11:53:09.957508+00:00
-- url     : https://prove2.me/submissions/62b15086-e9f5-4b2f-bcea-367e2b29e7bd

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P70
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Intake100.P70

attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint)
open QAlgorithms.Papers.Independent.Information100.P07 (positivePart negativePart)
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

theorem _root_.solution {I : Type*} [Fintype I] [Nonempty I]
    {m : ℕ} (hm : 0 < m)
    (E : Op I →ₗ[ℂ] Op I) (z : ℂ) (v : Fin m → Op I) (hv : IsJordanChain E z v) :
    E (v ⟨0, hm⟩) = z • v ⟨0, hm⟩ ∧
    ∀ X ∈ Submodule.span ℂ (Set.range v), ∀ w : ℂ, X ≠ 0 →
      (E X = w • X ↔ w = z ∧ ∃ c : ℂ, c ≠ 0 ∧ X = c • v ⟨0, hm⟩) := by
  obtain ⟨hli, hE⟩ := hv
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have h0 : E (v ⟨0, hm⟩) = z • v ⟨0, hm⟩ := by
    rw [hE]; simp
  refine ⟨h0, ?_⟩
  intro X hX w hX0
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hX
  let d : Fin (m'+1) → ℂ := fun i => if h : i.val + 1 < m' + 1 then c ⟨i.val + 1, h⟩ else 0
  have S : ∑ i : Fin (m'+1), c i • (if h : i.val = 0 then (0 : Op I) else v ⟨i.val - 1, by omega⟩) =
      ∑ i : Fin (m'+1), d i • v i := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
    simp [d]
    rfl
  have key : E X - w • X = ∑ i : Fin (m'+1), ((z - w) * c i + d i) • v i := by
    rw [← hc, map_sum]
    simp only [map_smul, hE, smul_add, Finset.sum_add_distrib, S, Finset.smul_sum, ← Finset.sum_sub_distrib]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [add_smul, sub_mul, sub_smul, mul_smul, mul_smul, smul_comm z (c i)]
    abel
  have coef : E X = w • X → ∀ i, (z - w) * c i + d i = 0 := by
    intro h
    have : ∑ i : Fin (m'+1), ((z - w) * c i + d i) • v i = 0 := by rw [← key, h, sub_self]
    exact Fintype.linearIndependent_iff.1 hli _ this
  constructor
  · intro h
    have hg := coef h
    by_cases hwz : w = z
    · refine ⟨hwz, c 0, ?_, ?_⟩
      · intro hc0
        apply hX0
        rw [← hc, Fin.sum_univ_succ]
        have : ∀ i : Fin m', c i.succ = 0 := by
          intro i
          have := hg (Fin.castSucc i)
          simp only [hwz, sub_self, zero_mul, zero_add, d, Fin.val_castSucc, add_lt_add_iff_right, i.isLt,
            dite_true] at this
          exact this
        simp [this, hc0]
      · rw [← hc, Fin.sum_univ_succ]
        have : ∀ i : Fin m', c i.succ = 0 := by
          intro i
          have := hg (Fin.castSucc i)
          simp only [hwz, sub_self, zero_mul, zero_add, d, Fin.val_castSucc, add_lt_add_iff_right, i.isLt,
            dite_true] at this
          exact this
        simp [this]
    · exfalso
      apply hX0
      have hzw : z - w ≠ 0 := sub_ne_zero.2 (Ne.symm hwz)
      have hall : ∀ i : Fin (m'+1), c i = 0 := by
        intro i
        induction i using Fin.reverseInduction with
        | last =>
          have := hg (Fin.last m')
          simp only [d, Fin.val_last, lt_self_iff_false, dite_false, add_zero] at this
          exact (mul_eq_zero.1 this).resolve_left hzw
        | cast i ih =>
          have := hg (Fin.castSucc i)
          simp only [d, Fin.val_castSucc, add_lt_add_iff_right, i.isLt, dite_true] at this
          have e : (⟨i.val + 1, by omega⟩ : Fin (m'+1)) = i.succ := rfl
          rw [e, ih, add_zero] at this
          exact (mul_eq_zero.1 this).resolve_left hzw
      rw [← hc]; simp [hall]
  · rintro ⟨rfl, c', _, rfl⟩
    rw [map_smul, h0, smul_comm]

end QAlgorithms.Papers.Independent.Intake100.P70
