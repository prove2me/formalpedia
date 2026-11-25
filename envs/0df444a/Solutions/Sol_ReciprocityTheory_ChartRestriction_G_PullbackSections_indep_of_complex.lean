-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.indep_of_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:55:26.814589+00:00
-- url     : https://prove2.me/submissions/52d54e38-4deb-45c4-bf22-886da73f3598

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_JInjCore
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DetAlg
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_IndepPts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_evalAt_eq_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_detAlg_holds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_indepDescent_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.TB
variable {K : Type} [Field K]
  (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
  (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
    (S →ₐ[K] T) → pts S → pts T → Prop)
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution [Algebra K ℂ] (hWD : EvalWD pts mapR)
    (hBC : ∀ (p : TRing K) (φ : p.R →ₐ[K] ℂ) (y : pts p.R), ∃ z : pts ℂ, mapR φ y z)
    {n : ℕ} (b : Fin n → Rules pts) (hnat : ∀ i, IsNatural pts mapR (b i)) (hb : LinearIndependent K b)
    (c : Fin n → ℂ) (hc : ∀ z : pts ℂ, FromTest pts mapR z → ∑ i, c i * evalAt pts mapR (b i) z = 0) :
    c = 0 := by
  classical
  haveI : CharZero K := (algebraMap K ℂ).charZero
  let F := AlgebraicClosure K
  haveI : IsAlgClosed ℂ := Complex.isAlgClosed
  haveI : Normal K F := IsAlgClosure.normal K F
  haveI : Algebra.IsSeparable K F := IsAlgClosure.separable K F
  haveI : IsGalois K F := ⟨⟩
  let ι : F →ₐ[K] ℂ := IsAlgClosed.lift
  let Pt := Σ p : TRing K, pts p.R × (p.R →ₐ[K] F)
  let v : Rules pts →ₗ[K] (Pt → F) :=
    { toFun := fun f q => q.2.2 (f q.1 q.2.1)
      map_add' := by
        intro f g; funext q
        change q.2.2 (f q.1 q.2.1 + g q.1 q.2.1) = q.2.2 (f q.1 q.2.1) + q.2.2 (g q.1 q.2.1)
        exact map_add _ _ _
      map_smul' := by
        intro a f; funext q
        change q.2.2 (a • f q.1 q.2.1) = a • q.2.2 (f q.1 q.2.1)
        exact map_smul _ _ _ }
  let act : (F ≃ₐ[K] F) → Pt → Pt := fun g q => ⟨q.1, q.2.1, (g : F →ₐ[K] F).comp q.2.2⟩
  have hbij : ∀ g, Function.Bijective (act g) := by
    intro g
    refine Function.bijective_iff_has_inverse.mpr ⟨act g.symm, ?_, ?_⟩
    · rintro ⟨p, y, φ⟩
      exact Sigma.ext rfl (heq_of_eq (Prod.ext rfl (AlgHom.ext fun r => by simp [act])))
    · rintro ⟨p, y, φ⟩
      exact Sigma.ext rfl (heq_of_eq (Prod.ext rfl (AlgHom.ext fun r => by simp [act])))
  have heq : ∀ g f y, v f (act g y) = g (v f y) := fun _ _ _ => rfl
  have hinj : Function.Injective v := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf0
    funext p y
    apply detAlg_holds K p.n p.I p.3 (f p y)
    intro L _ _ _ φ
    let e : L →ₐ[K] F := IsAlgClosed.lift
    have h1 : e (φ (f p y)) = 0 := congrFun hf0 ⟨p, y, e.comp φ⟩
    exact e.toRingHom.injective (h1.trans (map_zero e).symm)
  have hli := indepDescent_holds K F ι.toRingHom (Rules pts) Pt v act hbij heq hinj n b hb
  rw [Fintype.linearIndependent_iff] at hli
  funext i
  refine hli c ?_ i
  funext q
  obtain ⟨p, y, φ⟩ := q
  let ψ : p.R →ₐ[K] ℂ := ι.comp φ
  obtain ⟨z, hz⟩ := hBC p ψ y
  have h0 := hc z ⟨p, ψ, y, hz⟩
  simp only [evalAt_eq_of pts mapR hWD (b _) (hnat _) p ψ y z hz] at h0
  simpa [Finset.sum_apply, v, ψ] using h0
end ReciprocityTheory.ChartRestriction.G.PullbackSections
