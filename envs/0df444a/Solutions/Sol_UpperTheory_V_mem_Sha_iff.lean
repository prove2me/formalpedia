-- Prove2me | solution 1 for UpperTheory.V.mem_Sha_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:11:27.484691+00:00
-- url     : https://prove2.me/submissions/af829a17-f9b9-4f63-a1ee-7cccd91b3b8c

import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PartsConj
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_ReciprocityTheory_Gal_mem_Sel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology
open UpperTheory UpperTheory.V
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
variable {τ : F ≃+* F} {σ : Ω ≃+* Ω}
variable [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
namespace UpperTheory.V
theorem _root_.solution (D : LData F Ω l) (e : ℤ) (x : H1 (qzTw D e)) :
    x ∈ Sha D e ↔ ∀ v, resH1 (qzTw D e) (locFam D.S D.A v) (continuous_locFam D.S D.A v) x = 0 := by
  first
    | exact mem_Sha1 _ _ _ _
    | exact (mem_Sel _ _ _ _ _).trans (forall_congr' fun v => Submodule.mem_bot _)
    | exact (Submodule.mem_iInf _).trans (forall_congr' fun v => LinearMap.mem_ker)
    | (simp [Sha, Sha1, mem_Sel]; done)
end UpperTheory.V
