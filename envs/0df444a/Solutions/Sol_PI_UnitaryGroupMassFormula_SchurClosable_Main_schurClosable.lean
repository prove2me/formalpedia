-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.SchurClosable.Main.schurClosable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:03:56.42336+00:00
-- url     : https://prove2.me/submissions/9e17a89d-e156-4e20-9a07-2c3ccaff1cfc

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_HaarTransfer_SchurClosable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurUnitaryInner_UnitaryInner
import Theorems.Thm_PI_UnitaryGroupMassFormula_SchurClosable_Main_unitary_inner
import Theorems.Thm_PI_UnitaryGroupMassFormula_SchurClosable_Main_alg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.SchurClosable PI.UnitaryGroupMassFormula.SchurClosable.Main
open Filter Topology
namespace PI.UnitaryGroupMassFormula.SchurClosable.Main
theorem _root_.solution : Formalism.IndefR.Leaf.SchurClosable := by
  intro G H H' _ _ _ _ _ _ _ π π' hπ hπ' hirr D A hD hinv hint hclos
  let e := WithLp.prodContinuousLinearEquiv 2 ℂ H H'
  let gr : D →ₗ[ℂ] WithLp 2 (H × H') := e.symm.toLinearEquiv.toLinearMap ∘ₗ (D.subtype.prod A)
  have hgr : ∀ x : D, gr x = WithLp.toLp 2 ((x : H), A x) := fun x => rfl
  let Γ₀ : Submodule ℂ (WithLp 2 (H × H')) := LinearMap.range gr
  have hgrΓ : ∀ x : D, gr x ∈ Γ₀.topologicalClosure :=
    fun x => Γ₀.le_topologicalClosure (LinearMap.mem_range_self gr x)

  let U : G → (WithLp 2 (H × H') →L[ℂ] WithLp 2 (H × H')) := fun g =>
    e.symm.toContinuousLinearMap ∘L ((π g).prodMap (π' g)) ∘L e.toContinuousLinearMap
  have hU : ∀ g v, U g v = WithLp.toLp 2 (π g (WithLp.ofLp v).1, π' g (WithLp.ofLp v).2) :=
    fun g v => rfl
  have hUΓ : ∀ g, ∀ v ∈ Γ₀.topologicalClosure, U g v ∈ Γ₀.topologicalClosure := by
    intro g
    have hle : Γ₀ ≤ (Γ₀.topologicalClosure).comap
        (U g : WithLp 2 (H × H') →ₗ[ℂ] WithLp 2 (H × H')) := by
      rintro _ ⟨x, rfl⟩
      show U g (gr x) ∈ Γ₀.topologicalClosure
      have : U g (gr x) = gr ⟨π g x, hinv g x x.2⟩ := by
        simp only [hU, hgr]
        rw [hint g x (hinv g x x.2)]
      rw [this]
      exact hgrΓ _
    have hcl : IsClosed (((Γ₀.topologicalClosure).comap
        (U g : WithLp 2 (H × H') →ₗ[ℂ] WithLp 2 (H × H')) : Submodule ℂ _) :
        Set (WithLp 2 (H × H'))) := by
      exact Γ₀.isClosed_topologicalClosure.preimage (U g).continuous
    exact fun v hv => Submodule.topologicalClosure_minimal Γ₀ hle hcl hv
  have hUinner : ∀ g v w, inner ℂ (U g v) (U g w) = inner ℂ v w := by
    intro g v w
    simp only [hU, WithLp.prod_inner_apply, unitary_inner (π g) (hπ g),
      unitary_inner (π' g) (hπ' g)]
  have hπinv : ∀ g x, π g (π g⁻¹ x) = x := by
    intro g x
    show (π g * π g⁻¹) x = x
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  have hπ'inv : ∀ g x, π' g (π' g⁻¹ x) = x := by
    intro g x
    show (π' g * π' g⁻¹) x = x
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  have hUinv : ∀ g w, U g (U g⁻¹ w) = w := by
    intro g w
    simp only [hU, hπinv, hπ'inv, Prod.mk.eta, WithLp.toLp_ofLp]

  have hPcomm : ∀ g h, (Γ₀.topologicalClosure).starProjection (WithLp.toLp 2 (π g h, (0 : H')))
      = U g ((Γ₀.topologicalClosure).starProjection (WithLp.toLp 2 (h, (0 : H')))) := by
    intro g h
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact hUΓ g _ ((Γ₀.topologicalClosure).starProjection_apply_mem _)
    · intro w hw
      have h1 : WithLp.toLp 2 (π g h, (0 : H')) = U g (WithLp.toLp 2 (h, (0 : H'))) := by
        simp [hU]
      rw [h1, ← hUinv g w, ← map_sub, hUinner]
      exact Submodule.starProjection_inner_eq_zero (K := Γ₀.topologicalClosure) _ _
        (hUΓ g⁻¹ w hw)

  let M : H →L[ℂ] H := (ContinuousLinearMap.fst ℂ H H') ∘L e.toContinuousLinearMap ∘L
      (Γ₀.topologicalClosure).starProjection ∘L e.symm.toContinuousLinearMap ∘L
      (ContinuousLinearMap.inl ℂ H H')
  have hM : ∀ h, M h =
      (WithLp.ofLp ((Γ₀.topologicalClosure).starProjection (WithLp.toLp 2 (h, (0 : H'))))).1 :=
    fun h => rfl
  have hMc : ∀ g, M.comp (π g) = (π g).comp M := by
    intro g
    ext h
    simp only [ContinuousLinearMap.comp_apply, hM, hPcomm, hU, WithLp.ofLp_toLp]
  obtain ⟨c₀, hc₀⟩ := hirr M hMc
  have hMx : ∀ h, M h = c₀ • h := fun h => by rw [hc₀]; simp

  have hinj : ∀ v ∈ Γ₀.topologicalClosure, (WithLp.ofLp v).1 = 0 → v = 0 := by
    intro v hv h1
    have hv' : v ∈ closure (Γ₀ : Set (WithLp 2 (H × H'))) := by
      rwa [← Submodule.topologicalClosure_coe]
    obtain ⟨s, hs, hlim⟩ := mem_closure_iff_seq_limit.mp hv'
    choose u hu using fun n => LinearMap.mem_range.mp (hs n)
    have hc1 : Continuous (fun v : WithLp 2 (H × H') => (WithLp.ofLp v).1) :=
      continuous_fst.comp (WithLp.prod_continuous_ofLp ..)
    have hc2 : Continuous (fun v : WithLp 2 (H × H') => (WithLp.ofLp v).2) :=
      continuous_snd.comp (WithLp.prod_continuous_ofLp ..)
    have t1 : Tendsto (fun n => ((u n : D) : H)) atTop (𝓝 0) := by
      have := (hc1.tendsto v).comp hlim
      rw [h1] at this
      refine this.congr (fun n => ?_)
      simp [Function.comp, ← hu n, hgr]
    have t2 : Tendsto (fun n => A (u n)) atTop (𝓝 (WithLp.ofLp v).2) := by
      refine ((hc2.tendsto v).comp hlim).congr (fun n => ?_)
      simp [Function.comp, ← hu n, hgr]
    have h2 := hclos u _ t1 t2
    have h3 : WithLp.ofLp v = 0 := Prod.ext h1 h2
    calc v = WithLp.toLp 2 (WithLp.ofLp v) := rfl
      _ = 0 := by rw [h3]; rfl

  have hPx : ∀ x : D, (Γ₀.topologicalClosure).starProjection (WithLp.toLp 2 ((x : H), (0 : H')))
      = c₀ • gr x := by
    intro x
    have hmem : (Γ₀.topologicalClosure).starProjection (WithLp.toLp 2 ((x : H), (0 : H')))
        - c₀ • gr x ∈ Γ₀.topologicalClosure :=
      Submodule.sub_mem _ ((Γ₀.topologicalClosure).starProjection_apply_mem _)
        (Submodule.smul_mem _ c₀ (hgrΓ x))
    have hfst : (WithLp.ofLp ((Γ₀.topologicalClosure).starProjection
        (WithLp.toLp 2 ((x : H), (0 : H'))) - c₀ • gr x)).1 = 0 := by
      have := hMx x
      rw [hM] at this
      simp [hgr]
      exact sub_eq_zero.mpr this
    exact sub_eq_zero.mp (hinj _ hmem hfst)
  have hK : ∀ x y : D, inner ℂ (x : H) (y : H)
      = (starRingEnd ℂ c₀) * (inner ℂ (x : H) (y : H) + inner ℂ (A x) (A y)) := by
    intro x y
    have h0 := Submodule.starProjection_inner_eq_zero (K := Γ₀.topologicalClosure)
      (WithLp.toLp 2 ((x : H), (0 : H'))) (gr y) (hgrΓ y)
    rw [inner_sub_left, sub_eq_zero, hPx, inner_smul_left] at h0
    simp only [hgr, WithLp.prod_inner_apply, inner_zero_left, add_zero] at h0
    exact h0
  exact alg D A _ hK
end PI.UnitaryGroupMassFormula.SchurClosable.Main
