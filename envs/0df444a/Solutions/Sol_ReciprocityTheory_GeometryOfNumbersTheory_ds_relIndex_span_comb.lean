-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.ds_relIndex_span_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:02:08.751686+00:00
-- url     : https://prove2.me/submissions/46f12674-0e66-42a9-a328-1fe7e80c4275

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_DegStA
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_DegStB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open NumberField Module
open scoped ComplexOrder Matrix
variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution {r : ℕ} {v : Fin r → V} (hv : LinearIndependent K v)
    (g : Matrix (Fin r) (Fin r) (𝓞 K)) (hg : g.det ≠ 0) :
    (Submodule.span (𝓞 K) (Set.range fun j => ∑ i, g i j • v i)).toAddSubgroup.relIndex
      (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup = (Algebra.norm ℤ g.det).natAbs := by
  classical
  have hvO : LinearIndependent (𝓞 K) v := hv.restrict_scalars' (𝓞 K)
  let Φ : (Fin r → 𝓞 K) →+ V :=
    { toFun := fun c => ∑ i, c i • v i
      map_zero' := by simp
      map_add' := fun a b => by simp [add_smul, Finset.sum_add_distrib] }
  have hΦ : ∀ c, Φ c = ∑ i, c i • v i := fun c => rfl
  have hΦinj : Function.Injective Φ := by
    intro a b hab
    have h0 : ∑ i, (a - b) i • v i = 0 := by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
      rw [← hΦ, ← hΦ, hab, sub_self]
    funext i
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hvO _ h0 i)
  have hrange : (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup = AddSubgroup.map Φ ⊤ := by
    rw [← AddMonoidHom.range_eq_map]
    ext x
    simp only [Submodule.mem_toAddSubgroup, AddMonoidHom.mem_range,
      Submodule.mem_span_range_iff_exists_fun, hΦ]
  have hcomb : ∀ d : Fin r → 𝓞 K, Φ (g.mulVec d) = ∑ j, d j • ∑ i, g i j • v i := by
    intro d
    simp only [hΦ, Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by rw [mul_comm]
  have hcomap : AddSubgroup.comap Φ
      (Submodule.span (𝓞 K) (Set.range fun j => ∑ i, g i j • v i)).toAddSubgroup =
      (LinearMap.range (Matrix.mulVecLin g)).toAddSubgroup := by
    ext c
    simp only [AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup, LinearMap.mem_range,
      Matrix.mulVecLin_apply, Submodule.mem_span_range_iff_exists_fun]
    constructor
    · rintro ⟨d, hd⟩
      exact ⟨d, hΦinj (by rw [hcomb, hd])⟩
    · rintro ⟨d, rfl⟩
      exact ⟨d, (hcomb d).symm⟩
  have hTinj : Function.Injective (Matrix.mulVecLin g) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    by_contra hc0
    exact hg (Matrix.exists_mulVec_eq_zero_iff.1 ⟨c, hc0, hc⟩)
  let T : (Fin r → 𝓞 K) →ₗ[ℤ] (Fin r → 𝓞 K) := (Matrix.mulVecLin g).restrictScalars ℤ
  let N : Submodule ℤ (Fin r → 𝓞 K) := LinearMap.range T
  let e : (Fin r → 𝓞 K) ≃ₗ[ℤ] N := LinearEquiv.ofInjective T hTinj
  have hcard := Submodule.natAbs_det_equiv N e
  have hcomp : N.subtype ∘ₗ ((e : (Fin r → 𝓞 K) →+ N)).toIntLinearMap = T :=
    LinearMap.ext fun c => rfl
  rw [hcomp] at hcard
  have hdetT : LinearMap.det T = Algebra.norm ℤ g.det := by
    rw [LinearMap.det_restrictScalars, ← LinearMap.det_toLin' g]
    rfl
  calc _ = (Submodule.span (𝓞 K) (Set.range fun j => ∑ i, g i j • v i)).toAddSubgroup.relIndex
        (AddSubgroup.map Φ ⊤) := by rw [hrange]
    _ = (AddSubgroup.comap Φ (Submodule.span (𝓞 K)
          (Set.range fun j => ∑ i, g i j • v i)).toAddSubgroup).relIndex ⊤ :=
        (AddSubgroup.relIndex_comap _ _ _).symm
    _ = (LinearMap.range (Matrix.mulVecLin g)).toAddSubgroup.index := by
        rw [AddSubgroup.relIndex_top_right, hcomap]
    _ = Nat.card ((Fin r → 𝓞 K) ⧸ N) := rfl
    _ = _ := by rw [← hcard, hdetT]
end ReciprocityTheory.GeometryOfNumbersTheory
