-- Prove2me | solution 1 for ReciprocityTheory.Coh.shpPush_bij
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:48:24.429846+00:00
-- url     : https://prove2.me/submissions/fb087cfb-c8b5-472b-92ed-e0c8e9e4836c

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogIso
import Definitions.Def_ReciprocityTheory_GroupCohomology_PrismOpZeroEval
import Definitions.Def_ReciprocityTheory_GroupCohomology_Shapiro
import Theorems.Thm_ReciprocityTheory_Coh_shpPush_apply
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_H_cls
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_Z_apply
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_comp_f
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_id_H
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_id_f
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_add
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_d
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_eq_zero_iff
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_neg
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_smul
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_sub
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.H_cls
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.Z_apply
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.comp_f
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.id_H
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.id_f
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_add
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_d
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_eq_zero_iff
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_neg
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_smul
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_sub
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_zero



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {U : Subgroup G} {M : TRep R U} {C : TRep R G} (ev : Pair C M) (hφ : ev.φ = U.subtype)
variable (j : C.V → C(G, M.V)) (hj : Topology.IsEmbedding j) (hjc : ∀ c g, j c g = ev.u (C.rho g c))
  (hr : ∀ f : C(G, M.V), (∀ (x : U) g, f (x * g) = M.rho x (f g)) → f ∈ Set.range j)
include hj hjc hr
namespace ReciprocityTheory.Coh
theorem _root_.solution (n : ℕ) : Bijective (shpPush ev hφ n) := by
  constructor
  · intro F F' hFF'
    apply Subtype.ext
    funext p
    apply hj.injective
    ext g
    rw [hjc, hjc, ← F.2.2 g p, ← F'.2.2 g p]
    have h' := congrArg (fun K : hcoch M G n => K.1 fun i => g • p i) hFF'
    simpa only [shpPush_apply] using h'
  · intro K
    have hKc : Continuous K.1 := K.2.1
    let m2 : C((Fin (n + 1) → G) × G, M.V) := ⟨fun q => K.1 fun i => q.2 * q.1 i,
      hKc.comp (continuous_pi fun i => continuous_snd.mul ((continuous_apply i).comp continuous_fst))⟩
    let Φ : (Fin (n + 1) → G) → C(G, M.V) := fun q => ContinuousMap.curry m2 q
    have hΦ : Continuous Φ := (ContinuousMap.curry m2).continuous
    have hΦr : ∀ q, ∃ c, j c = Φ q := by
      intro q
      refine hr _ fun u g => ?_
      show K.1 (fun i => (u : G) * g * q i) = M.rho u (K.1 fun i => g * q i)
      have h' := K.2.2 u (fun i => g * q i)
      simp only [mul_assoc]
      exact h'
    choose c hc using hΦr
    have hcont : Continuous c := by
      refine hj.isInducing.continuous_iff.2 ?_
      have hjc' : j ∘ c = Φ := funext hc
      rw [hjc']
      exact hΦ
    have hequiv : ∀ (g : G) q, c (fun i => g • q i) = C.rho g (c q) := by
      intro g q
      apply hj.injective
      ext h
      have e1 : C.rho h (C.rho g (c q)) = C.rho (h * g) (c q) := by
        rw [map_mul]
        rfl
      rw [hc, hjc, e1, ← hjc, hc]
      show K.1 (fun i => h * (g • q i)) = K.1 (fun i => h * g * q i)
      simp only [smul_eq_mul, mul_assoc]
    refine ⟨⟨c, hcont, hequiv⟩, Subtype.ext (funext fun q => ?_)⟩
    show ev.u (c q) = K.1 q
    have h' := congrArg (fun f : C(G, M.V) => f 1) (hc q)
    simp only [hjc, map_one, Module.End.one_apply] at h'
    rw [h']
    show K.1 (fun i => 1 * q i) = K.1 q
    simp only [one_mul]
end ReciprocityTheory.Coh
