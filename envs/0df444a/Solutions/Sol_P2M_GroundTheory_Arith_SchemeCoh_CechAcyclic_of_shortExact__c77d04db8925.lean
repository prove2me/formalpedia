-- Prove2me | solution 1 for P2M_GroundTheory_Arith_SchemeCoh_CechAcyclic_of_shortExact__c77d04db8925
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:33:57.381347+00:00
-- url     : https://prove2.me/submissions/97fe3c80-78cc-40a8-9f4b-4efe6c6a7a82

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InjectiveCech
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_Cartan
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_d_d
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_push_comp
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_push_d
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_push_injective
import Theorems.Thm_P2M_GroundTheory_Arith_SchemeCoh_push_zero__4bd36dbeb085


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory Opposite TopologicalSpace Limits
universe w u
variable {X : TopCat.{u}}
variable (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
  (hP : Presheaf.IsSheaf (Opens.grothendieckTopology X) P)
variable {P}
namespace GroundTheory.Arith.SchemeCoh
namespace CechAcyclic
theorem _root_.solution {ι : Type w} (U : ι → Opens X)
    {F I Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (f : F ⟶ I) (g : I ⟶ Q) (hfg : f ≫ g = 0)
    (hinj : ∀ {n : ℕ} (i : Fin (n + 1) → ι), Function.Injective (f.app (op (inter U i))))
    (hex : ∀ {n : ℕ} (i : Fin (n + 1) → ι) (y : I.obj (op (inter U i))),
      g.app _ y = 0 → ∃ x, f.app _ x = y)
    (hsurj : ∀ {n : ℕ} (i : Fin (n + 1) → ι), Function.Surjective (g.app (op (inter U i))))
    (hF : CechAcyclic F U) (hI : CechAcyclic I U) : CechAcyclic Q U := by
  intro n σ hσ
  choose τ hτ using fun i => hsurj i (σ i)
  have hτ' : push U g (n + 1) τ = σ := funext hτ
  have h0 : push U g (n + 2) (d I U (n + 1) τ) = 0 := by rw [push_d, hτ', hσ]
  choose ρ hρ using fun j => hex j _ (congrFun h0 j)
  have hρ' : push U f (n + 2) ρ = d I U (n + 1) τ := funext hρ
  have hρc : d F U (n + 2) ρ = 0 := by
    apply push_injective U f (n + 3) (fun j => hinj j)
    rw [map_zero, push_d, hρ', d_d]
  obtain ⟨α, hα⟩ := hF (n + 1) ρ hρc
  have hc : d I U (n + 1) (τ - push U f (n + 1) α) = 0 := by
    rw [map_sub, ← push_d, hα, hρ', sub_self]
  obtain ⟨β, hβ⟩ := hI n _ hc
  refine ⟨push U g n β, ?_⟩
  rw [← push_d, hβ, map_sub, hτ', push_comp, hfg, push_zero', sub_zero]
end CechAcyclic
end GroundTheory.Arith.SchemeCoh
