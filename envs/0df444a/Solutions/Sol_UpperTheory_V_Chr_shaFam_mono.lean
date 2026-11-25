-- Prove2me | solution 1 for UpperTheory.V.Chr.shaFam_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:02:04.056882+00:00
-- url     : https://prove2.me/submissions/173e51ce-32f9-4765-94e7-be27c0ac035c

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_SelmerTransport_ConjStableShaFam
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PrimeSetBoundDataOfPrimitiveChar
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_CharacterLevelBounds_ShaFamMono
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.Base
open UpperTheory UpperTheory.V UpperTheory.V.Chr
variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] (l : ℕ) [Fact l.Prime]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O]
omit [Fact l.Prime]
namespace UpperTheory.V.Chr
theorem _root_.solution {m n : ℕ} (h : m ∣ n) : shaFam k Ω m ⊆ shaFam k Ω n := by
  intro U hU
  simp only [shaFam, Set.mem_setOf_eq] at hU ⊢
  rcases hU with ⟨A, hA, rfl⟩ | ⟨A, rfl⟩
  · left
    refine ⟨A, ?_, rfl⟩
    obtain ⟨c, rfl⟩ := h
    have hc : A.valuation (c : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (natCast_mem A c)
    push_cast
    rw [map_mul]
    calc A.valuation (m : Ω) * A.valuation (c : Ω) ≤ A.valuation (m : Ω) * 1 := by gcongr
      _ = A.valuation (m : Ω) := mul_one _
      _ < 1 := hA
  · right
    exact ⟨A, rfl⟩
end UpperTheory.V.Chr
