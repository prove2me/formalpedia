-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P21.completelyEntangledSubspace
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T03:40:54.925185+00:00
-- url     : https://prove2.me/submissions/a2a2cd12-0c2a-4c58-a7e6-1a037523a037

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

lemma x8_coord (c : Fin 2 → ℂ) (a : Fin 2) (b : Fin 3) :
    (∑ i, c i • entangledPair i) (a, b) =
      (if (a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 1) then c 0 else 0) +
      (if (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2) then c 1 else 0) := by
  fin_cases a <;> fin_cases b <;>
    simp [Fin.sum_univ_two, entangledPair, QAlgorithms.ket, PiLp.single_apply]

theorem x8_main :
    Module.finrank ℂ (Submodule.span ℂ (Set.range entangledPair)) = 2 ∧
    ∀ p : Vec QT, p ∈ Submodule.span ℂ (Set.range entangledPair) → p ≠ 0 →
      ¬∃ (e : Vec (Fin 2)) (f : Vec (Fin 3)), p = tensor e f := by
  constructor
  · have hli : LinearIndependent ℂ entangledPair := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      have h0 := congrArg (fun v : Vec QT => v (0, 0)) hg
      have h1 := congrArg (fun v : Vec QT => v (0, 1)) hg
      simp only [x8_coord] at h0 h1
      simp at h0 h1
      fin_cases i
      · exact h0
      · exact h1
    rw [finrank_span_eq_card hli]
    simp
  · intro p hp hp0 ⟨e, f, hpef⟩
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hp
    have E : ∀ a b, (∑ i, c i • entangledPair i) (a, b) = e a * f b := by
      intro a b
      rw [hpef]; rfl
    have e00 := E 0 0
    have e01 := E 0 1
    have e02 := E 0 2
    have e10 := E 1 0
    have e11 := E 1 1
    have e12 := E 1 2
    simp only [x8_coord] at e00 e01 e02 e10 e11 e12
    simp at e00 e01 e02 e10 e11 e12
    apply hp0
    have hc : c = 0 := by
      by_cases he : e 0 = 0
      · ext i; fin_cases i
        · simp [e00, he]
        · simp [e01, he]
      · have hf2 : f 2 = 0 := by
          rcases e02 with h | h
          · exact absurd h he
          · exact h
        have hc1 : c 1 = 0 := by rw [e12, hf2, mul_zero]
        have hc0 : c 0 = 0 := by
          by_cases hf0 : f 0 = 0
          · rw [e00, hf0, mul_zero]
          · have he1 : e 1 = 0 := by
              rcases e10 with h | h
              · exact h
              · exact absurd h hf0
            rw [e11, he1, zero_mul]
        ext i; fin_cases i
        · simpa using hc0
        · simpa using hc1
    subst hc
    simp

end QAlgorithms.Papers.Independent.Information100.P21

open QAlgorithms.Papers.Independent.Information100.P21 in
attribute [local instance] Classical.propDecidable Classical.decEq in
theorem solution :
  Module.finrank ℂ (Submodule.span ℂ (Set.range entangledPair))=2 ∧
  ∀ p : Vec QT, p∈Submodule.span ℂ (Set.range entangledPair) → p≠0 →
    ¬∃ (e : Vec (Fin 2)) (f : Vec (Fin 3)), p=tensor e f :=
  QAlgorithms.Papers.Independent.Information100.P21.x8_main
