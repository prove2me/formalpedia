-- Prove2me | solution 1 for UpperTheory.V.h1TwistConjByLift_mem_sha_of_mem_sha
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:28:49.875245+00:00
-- url     : https://prove2.me/submissions/20413909-bde9-4719-9ebf-de17ccc38e0d

import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PartsConj
import Theorems.Thm_UpperTheory_V_conjGS_toGS
import Theorems.Thm_UpperTheory_V_exists_cocycle_h1TwistConjByLift_mk_eq_mk
import Theorems.Thm_UpperTheory_V_mem_Sha_iff
import Theorems.Thm_UpperTheory_V_res_mk_eq_zero_iff
import Theorems.Thm_UpperTheory_V_h1TwistConjByLift_eq_of_isLift_of_isLift
import Theorems.Thm_ReciprocityTheory_Gal_exists_smul_eq_of_isPlaceOver


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology
open UpperTheory UpperTheory.V
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
variable {τ : F ≃+* F} {σ : Ω ≃+* Ω}
variable [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
namespace UpperTheory.V
theorem _root_.solution (D : LData F Ω l) (e : ℤ) (h : IsLift τ σ) {x : H1 (qzTw D e)} (hx : x ∈ Sha D e) :
    h1TwistConjByLift D e h x ∈ Sha D e := by
  rw [mem_Sha_iff] at hx ⊢
  intro v
  have hw : preplace τ v.1 ∈ D.S := by
    rw [← Finset.mem_coe, D.hS, preplace_mem_Above, ← D.hS]
    exact v.2
  let w : D.S := ⟨_, hw⟩
  have hA : ∀ x, σ x ∈ D.A v ↔ x ∈ (D.A v).comap σ.toRingHom := fun x => Iff.rfl
  obtain ⟨g₀, hg₀⟩ := exists_smul_eq_of_isPlaceOver (F := F) (D.hA w) (isPlaceOver_preplace h hA (D.hA v))
  have h' : IsLift τ (g₀.toRingEquiv.trans σ) := fun y => by
    rw [RingEquiv.trans_apply, ← h]
    exact congrArg σ (g₀.commutes y)
  have hA' : ∀ x, (g₀.toRingEquiv.trans σ) x ∈ D.A v ↔ x ∈ D.A w := fun x => by
    refine (hA (g₀ x)).trans ?_
    rw [← hg₀, ← AlgEquiv.smul_def]
    exact ValuationSubring.smul_mem_pointwise_smul_iff
  rw [h1TwistConjByLift_eq_of_isLift_of_isLift D e h h']
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨z₁, e₁, f₁⟩ := exists_cocycle_h1TwistConjByLift_mk_eq_mk D e h' z
  obtain ⟨m, hm⟩ := (res_mk_eq_zero_iff D e w z).1 (hx w)
  rw [e₁]
  refine (res_mk_eq_zero_iff D e v z₁).2 ⟨twScal l (g₀.toRingEquiv.trans σ) e • m, fun g => ?_⟩
  rw [f₁, conjGS_toGS, hm ⟨_, conjGal_mem_Dec h' hA' g.2⟩, ← conjGS_toGS D h', qzTw_apply, chi_conjGS, map_smul,
    smul_sub, qzTw_apply]
end UpperTheory.V
