-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_chart_rel_f6b2a434feeb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:08:07.583796+00:00
-- url     : https://prove2.me/submissions/d8177b94-70b6-4504-bc1c-9e2113eca4b1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPluckerCover
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_wedge_eq_e255558b0259

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
variable {Ω : Type} [Field Ω] {ι : Type} (x : ι → Ω) (i : ι)
variable {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ}
namespace GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
theorem _root_.solution (B : ChartBundle ℤ x 2 E) (e : Module.Basis (Fin 2) Ω E) {κ ν : Type} [Fintype κ]
    (φ : κ → E →ₗ[Ω] Ω) (δ : ν → Ω)
    (hgen : ∀ ψ ∈ T.dualLat B i, ∃ c : κ → Ω, (∀ k, c k ∈ chartRing ℤ x i) ∧ ψ = ∑ k, c k • (x i)⁻¹ • φ k)
    (hdet : ∀ u ∈ B.lat i, ∀ w ∈ B.lat i,
      T.detE e u w ∈ Submodule.span (chartRing ℤ x i) (Set.range fun l => (x i)⁻¹ * δ l))
    {f : Ω} (hf : f ∈ chartRing ℤ x i) (bb : Fin 2 → E) (hli : LinearIndependent Ω bb)
    (hsp : Submodule.span Ω (Set.range bb) = ⊤) (hgenb : ∀ q, ∃ n : ℕ, f ^ n • bb q ∈ B.lat i) (M : ℕ)
    (hM : ∀ v ∈ B.lat i, ∀ q, f ^ M * (Module.Basis.mk hli hsp.ge).repr v q ∈ chartRing ℤ x i) :
    ∃ n : ℕ, f ^ n ∈ Submodule.span (chartRing ℤ x i) (Set.range fun t : κ × κ × ν =>
      (x i)⁻¹ ^ 3 * (φ t.1 (e 0) * φ t.2.1 (e 1) - φ t.1 (e 1) * φ t.2.1 (e 0)) * δ t.2.2) := by
  classical
  set Rg := chartRing ℤ x i
  set J := Submodule.span Rg (Set.range fun t : κ × κ × ν =>
      (x i)⁻¹ ^ 3 * (φ t.1 (e 0) * φ t.2.1 (e 1) - φ t.1 (e 1) * φ t.2.1 (e 0)) * δ t.2.2)
  have smulR : ∀ (a : Ω), a ∈ Rg → ∀ v : Ω, v ∈ J → a * v ∈ J := fun a ha v hv => by
    have := J.smul_mem (⟨a, ha⟩ : Rg) hv
    rwa [Subalgebra.smul_def, smul_eq_mul] at this
  obtain ⟨n0, hn0⟩ := hgenb 0
  obtain ⟨n1, hn1⟩ := hgenb 1
  have hpad0 : f ^ (n0 + n1) • bb 0 ∈ B.lat i := by
    rw [show f ^ (n0 + n1) • bb 0 = f ^ n1 • (f ^ n0 • bb 0) by rw [smul_smul, ← pow_add, add_comm]]
    exact B.stable i _ (pow_mem hf _) _ hn0
  have hpad1 : f ^ (n0 + n1) • bb 1 ∈ B.lat i := by
    rw [show f ^ (n0 + n1) • bb 1 = f ^ n0 • (f ^ n1 • bb 1) by rw [smul_smul, ← pow_add]]
    exact B.stable i _ (pow_mem hf _) _ hn1
  set β := Module.Basis.mk hli hsp.ge
  have hb : ∀ q, bb q = β q := fun q => (Module.Basis.mk_apply _ _ _).symm
  let ψ : Fin 2 → E →ₗ[Ω] Ω := fun q => f ^ M • β.coord q
  have hψ : ∀ q, ψ q ∈ T.dualLat B i := fun q v hv => by
    simpa [ψ] using hM v hv q
  obtain ⟨c0, hc0, h0⟩ := hgen _ (hψ 0)
  obtain ⟨c1, hc1, h1⟩ := hgen _ (hψ 1)
  set u := f ^ (n0 + n1) • bb 0
  set w := f ^ (n0 + n1) • bb 1
  have hval : ψ 0 u * ψ 1 w - ψ 0 w * ψ 1 u = f ^ (2 * M + 2 * (n0 + n1)) := by
    simp only [ψ, u, w, hb, LinearMap.smul_apply, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
      smul_eq_mul, Finsupp.single_apply]
    simp
    ring
  have hspan : ∀ k m, ∀ t ∈ Submodule.span Rg (Set.range fun l => (x i)⁻¹ * δ l),
      (x i)⁻¹ ^ 2 * (φ k (e 0) * φ m (e 1) - φ k (e 1) * φ m (e 0)) * t ∈ J := by
    intro k m t ht
    induction ht using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, rfl⟩ := hy
      refine Submodule.subset_span ⟨(k, m, l), ?_⟩
      simp only
      ring
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul a y _ hy =>
      rw [Subalgebra.smul_def, smul_eq_mul, mul_left_comm]
      exact smulR _ a.2 _ hy
  have hmem : ψ 0 u * ψ 1 w - ψ 0 w * ψ 1 u ∈ J := by
    rw [h0, h1]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.sum_mul_sum]
    rw [← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun m _ => ?_
    have key := wedge_eq e (φ k) (φ m) u w
    have : c0 k * ((x i)⁻¹ * φ k u) * (c1 m * ((x i)⁻¹ * φ m w)) -
        c0 k * ((x i)⁻¹ * φ k w) * (c1 m * ((x i)⁻¹ * φ m u)) =
        (c0 k * c1 m) * ((x i)⁻¹ ^ 2 * (φ k (e 0) * φ m (e 1) - φ k (e 1) * φ m (e 0)) * T.detE e u w) := by
      linear_combination (c0 k * c1 m * (x i)⁻¹ ^ 2) * key
    rw [this]
    exact smulR _ (mul_mem (hc0 k) (hc1 m)) _ (hspan k m _ (hdet u hpad0 w hpad1))
  exact ⟨_, hval ▸ hmem⟩
end GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
