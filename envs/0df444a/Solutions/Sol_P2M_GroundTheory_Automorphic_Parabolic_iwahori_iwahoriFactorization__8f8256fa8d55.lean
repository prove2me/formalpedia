-- Prove2me | solution 1 for P2M_GroundTheory_Automorphic_Parabolic_iwahori_iwahoriFactorization__8f8256fa8d55
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:54:03.185545+00:00
-- url     : https://prove2.me/submissions/4f364b36-9fd4-4d9a-b907-414b0c034793

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_iwahori_iwahoriFactorization
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_iwahoriFactorization_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {β}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (hβ : Monotone β) :
    ∀ k ∈ iwahori F n, ∃ x ∈ iwahori F n ⊓ unipotentRadical F n β,
      ∃ y ∈ iwahori F n ⊓ levi F n β, ∃ z ∈ iwahori F n ⊓ oppositeUnipotentRadical F n β,
        k = x * y * z :=
  iwahoriFactorization_symm (iwahori_iwahoriFactorization hβ)
end GroundTheory.Automorphic.Parabolic
