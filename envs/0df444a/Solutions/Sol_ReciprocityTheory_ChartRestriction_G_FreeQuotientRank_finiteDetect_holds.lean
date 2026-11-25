-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.finiteDetect_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:01:19.3702+00:00
-- url     : https://prove2.me/submissions/21f4efdc-8975-48b0-bb75-87256e825ec7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FiniteDetectStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FinDetPf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
theorem _root_.solution : FiniteDetectStatement := by
  intro L E _ _ _ _ W FF hkill hdet
  classical
  let S : Set (Submodule L E) :=
    {P | ∃ s : Finset (Module.Dual L E), ↑s ⊆ FF ∧ (⨅ c ∈ s, LinearMap.ker c) = P}
  have hS : S.Nonempty := ⟨_, ∅, by simp, rfl⟩
  obtain ⟨P, ⟨s, hsFF, rfl⟩, hmin⟩ := IsArtinian.set_has_minimal S hS
  refine ⟨s, hsFF, le_antisymm ?_ ?_⟩
  · intro x hx
    by_contra hxW
    obtain ⟨c, hcFF, hcx⟩ := hdet x hxW
    have hmem : (⨅ d ∈ insert c s, LinearMap.ker d) ∈ S :=
      ⟨insert c s, by
        intro d hd
        rcases Finset.mem_insert.mp hd with rfl | hd
        · exact hcFF
        · exact hsFF hd, rfl⟩
    apply hmin _ hmem
    refine lt_of_le_of_ne ?_ ?_
    · exact le_iInf₂ fun d hd => iInf₂_le d (Finset.mem_insert_of_mem hd)
    · intro heq
      have hx' : x ∈ ⨅ d ∈ insert c s, LinearMap.ker d := heq ▸ hx
      have : x ∈ LinearMap.ker c :=
        (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hx' c) (Finset.mem_insert_self c s)
      exact hcx this
  · exact le_iInf₂ fun c hc => hkill c (hsFF hc)
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
