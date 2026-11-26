-- Prove2me | solution 1 for TunnellMap.GloballyRanked.stable_exists_bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:48:29.352885+00:00
-- url     : https://prove2.me/submissions/c26c9c4f-3da3-4c0f-a559-2916699878a0

import Definitions.Def_TunnellMap_GloballyRanked
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_at_left
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_symm_at_right

set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*}
namespace TunnellMap.GloballyRanked
theorem _root_.solution [LinearOrder K] [Fintype S] [Fintype T]
    (I : GloballyRanked K S T) (hcard : Fintype.card S = Fintype.card T)
    (m : ℕ) (hm : Fintype.card S ≤ m) : ∃ M : S ≃ T, I.Stable M := by
  classical
  induction m generalizing S T with
  | zero =>
      have hs₀ : Fintype.card S = 0 := by omega
      letI : IsEmpty S := Fintype.card_eq_zero_iff.mp hs₀
      let M : S ≃ T := Fintype.equivOfCardEq hcard
      refine ⟨M, ?_⟩
      intro s
      exact isEmptyElim s
  | succ m ih =>
      by_cases hS : Nonempty S
      · letI : Nonempty S := hS
        have hspos : 0 < Fintype.card S := Fintype.card_pos_iff.mpr hS
        have htpos : 0 < Fintype.card T := by omega
        letI : Nonempty T := Fintype.card_pos_iff.mp htpos
        let E : Finset (S × T) := Finset.univ
        have hE : E.Nonempty := Finset.univ_nonempty
        let R : Finset K := E.image (fun e => I.rank e.1 e.2)
        have hR : R.Nonempty := hE.image _
        let k := R.min' hR
        have hkR : k ∈ R := Finset.min'_mem R hR
        obtain ⟨e₀, he₀E, he₀k⟩ := Finset.mem_image.mp hkR
        let s₀ := e₀.1
        let t₀ := e₀.2
        have hmin (s : S) (t : T) : I.rank s₀ t₀ ≤ I.rank s t := by
          have hr : I.rank s t ∈ R := Finset.mem_image.mpr ⟨(s, t), Finset.mem_univ _, rfl⟩
          rw [he₀k]
          change R.min' hR ≤ I.rank s t
          exact Finset.min'_le R (I.rank s t) hr
        let S' := {s : S // s ≠ s₀}
        let T' := {t : T // t ≠ t₀}
        let I' : GloballyRanked K S' T' :=
          { rank := fun s t => I.rank s.1 t.1
            source_injective := fun s _ _ h => Subtype.ext (I.source_injective s.1 h)
            target_injective := fun t _ _ h => Subtype.ext (I.target_injective t.1 h) }
        have hcardS' : Fintype.card S' = Fintype.card S - 1 := by
          simp [S']
        have hcardT' : Fintype.card T' = Fintype.card T - 1 := by
          simp [T']
        have hcard' : Fintype.card S' = Fintype.card T' := by omega
        have hm' : Fintype.card S' ≤ m := by omega
        obtain ⟨M', hM'⟩ := ih I' hcard' hm'
        let M : S ≃ T := insertEquiv s₀ t₀ M'
        refine ⟨M, ?_⟩
        intro s t hb
        by_cases hs : s = s₀
        · subst s
          have hlt : I.rank s₀ t < I.rank s₀ t₀ := by
            simpa [M] using hb.1
          exact (not_lt_of_ge (hmin s₀ t)) hlt
        · by_cases ht : t = t₀
          · subst t
            have hlt : I.rank s t₀ < I.rank s₀ t₀ := by
              simpa [M] using hb.2
            exact (not_lt_of_ge (hmin s t₀)) hlt
          · apply hM' ⟨s, hs⟩ ⟨t, ht⟩
            constructor
            · simpa [I', M, insertEquiv, hs] using hb.1
            · simpa [I', M, insertEquiv, ht] using hb.2
      · have hs₀ : Fintype.card S = 0 :=
          Fintype.card_eq_zero_iff.mpr (not_nonempty_iff.mp hS)
        letI : IsEmpty S := Fintype.card_eq_zero_iff.mp hs₀
        let M : S ≃ T := Fintype.equivOfCardEq hcard
        refine ⟨M, ?_⟩
        intro s
        exact isEmptyElim s
end TunnellMap.GloballyRanked
