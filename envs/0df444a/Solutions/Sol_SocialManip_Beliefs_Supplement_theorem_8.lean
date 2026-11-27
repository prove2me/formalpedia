-- Prove2me | solution 1 for SocialManip.Beliefs.Supplement.theorem_8
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:35:12.652132+00:00
-- url     : https://prove2.me/submissions/a8fb8ef1-9389-4496-b73a-dd80dcabdaf0

import Mathlib
import Definitions.Def_SocialManip_Beliefs_Setting
import Definitions.Def_SocialManip_Beliefs_Supplement_Network
import Definitions.Def_SocialManip_Beliefs_Supplement_Game
import Definitions.Def_SocialManip_Beliefs_Supplement_AppendixA

open MeasureTheory Filter Topology

open SocialManip
open SocialManip.Beliefs
open SocialManip.Beliefs.Supplement

open SocialManip.Beliefs

/-- The printed Assumption 2 permits no Bayesian agents. Its pure-interference branch of (*)
then asks for a member of the empty set. Positive normalized rows on an open set satisfy all
other assumptions, so an exceptional Lebesgue-null set cannot repair the omitted domain. -/
theorem solution :
    ∀ Z : Set ({i : Fin 2 // i ∉ (∅ : Finset (Fin 2))} → Fin 2 → ℝ), volume Z = 0 →
      ∃ M : AModel 2, M.Standing ∧ M.Assumption2 ∧ M.B = ∅ ∧
        M.q = 1 / 2 ∧ M.μ0 = 1 / 2 ∧ M.lamLow = 9 / 10 ∧ M.lamUp = 2 ∧
        (∀ i, M.lam i = 1) ∧ (∀ i, M.p i = 4 / 5) ∧
        (∀ i j, 0 < M.α i j) ∧ (∀ i, 0 < M.θ i) ∧
        degrootRows (∅ : Finset (Fin 2)) M.α ∉ Z ∧
        ∃ a : AAction 2, a.Admissible M ∧ a.1 ≠ State.S ∧ (∃ i, a.2.1 i = true) ∧
          ¬ ∃ i : Fin 2, i ∈ M.B := by
            classical
            intro Z hZ
            let U : Set ({i : Fin 2 // i ∉ (∅ : Finset (Fin 2))} → Fin 2 → ℝ) :=
              Set.univ.pi fun _ => Set.univ.pi fun _ => Set.Ioo (0 : ℝ) (1 / 3)
            have hUo : IsOpen U := by
              refine isOpen_set_pi Set.finite_univ fun _ _ => ?_
              exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo
            have hUn : U.Nonempty := by
              refine ⟨fun _ _ => 1 / 6, ?_⟩
              intro i _ j _
              constructor <;> norm_num
            have hUpos : 0 < volume U := hUo.measure_pos volume hUn
            have hnot : ¬ U ⊆ Z := by
              intro h
              have := measure_mono_null h hZ
              exact hUpos.ne' this
            obtain ⟨w, hwU, hwZ⟩ := Set.not_subset.mp hnot
            have hw : ∀ i j, 0 < w i j ∧ w i j < 1 / 3 := fun i j =>
              hwU i (Set.mem_univ _) j (Set.mem_univ _)
            let α : Matrix (Fin 2) (Fin 2) ℝ := fun i j => w ⟨i, by simp⟩ j
            have hα : ∀ i j, 0 < α i j ∧ α i j < 1 / 3 := fun i j => hw _ j
            have hθ : ∀ i, 0 < 1 - ∑ j, α i j := by
              intro i
              rw [Fin.sum_univ_two]
              have h0 := (hα i 0).2
              have h1 := (hα i 1).2
              linarith
            let M : AModel 2 :=
              { B := ∅
                θ := fun i => 1 - ∑ j, α i j
                α := α
                p := fun _ => 4 / 5
                q := 1 / 2
                μ0 := 1 / 2
                lam := fun _ => 1
                lamLow := 9 / 10
                lamUp := 2
                Δ := 1
                ε := 1
                b := 0
                N := fun _ => Finset.univ
                ν := fun _ => 0 }
            have hmax : M.lamMax = 1 := by
              show (⨆ _ : Fin 2, (1 : ℝ)) = 1
              exact ciSup_const
            refine ⟨M, ?_, ?_, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl,
              fun i j => (hα i j).1, hθ, hwZ, ?_⟩
            · refine ⟨fun i => ?_, fun i _ => (hθ i).le, fun i _ j => (hα i j).1.le, fun i _ => ?_,
                ?_, ?_, ?_, ?_, ?_, fun i => ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_, fun i _ j => ?_⟩
              · show (1 / 2 : ℝ) ≤ 4 / 5 ∧ (4 / 5 : ℝ) < 1
                norm_num
              · show 1 - ∑ j, α i j + ∑ j, α i j = 1
                ring
              · show (0 : ℝ) < 1 / 2
                norm_num
              · show (1 / 2 : ℝ) < 1
                norm_num
              · show (0 : ℝ) < 1 / 2
                norm_num
              · show (1 / 2 : ℝ) < 1
                norm_num
              · show (0 : ℝ) < 9 / 10
                norm_num
              · show (9 / 10 : ℝ) < 1
                norm_num
              · show (0 : ℝ) < 2
                norm_num
              · show (0 : ℝ) < 1
                norm_num
              · show (0 : ℝ) < 1
                norm_num
              · show (-1 : ℝ) < 0
                norm_num
              · show (0 : ℝ) < 1
                norm_num
              · exact absurd hi (Finset.notMem_empty i)
              · exact ⟨fun _ => (hα i j).1, fun _ => Finset.mem_univ j⟩
            · refine ⟨?_, fun i => ?_, ⟨0, ?_⟩, ⟨⟨0, ?_⟩, fun i _ => ?_⟩, fun i j _ => ?_⟩
              · rw [hmax]
                show (1 : ℝ) < 9 / 10 + 2 / 2
                norm_num
              · rw [hmax]
                show (4 / 5 : ℝ) < (2 + 1) / (2 * 1)
                norm_num
              · show ((2 : ℝ) + 9 / 10) / (2 * (9 / 10) + 2) < 4 / 5
                norm_num
              · show (1 / 2 : ℝ) < 4 / 5
                norm_num
              · refine ⟨fun _ => ?_, fun _ => hθ i⟩
                show (1 / 2 : ℝ) < 4 / 5
                norm_num
              · exact Relation.TransGen.single (Finset.mem_univ j)
            · refine ⟨(State.R, fun _ => true, fun _ => 1), fun i _ => ?_, ?_, ⟨0, rfl⟩, ?_⟩
              · show (0 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 2
                norm_num
              · show State.R ≠ State.S
                decide
              · rintro ⟨i, hi⟩
                exact absurd hi (Finset.notMem_empty i)
