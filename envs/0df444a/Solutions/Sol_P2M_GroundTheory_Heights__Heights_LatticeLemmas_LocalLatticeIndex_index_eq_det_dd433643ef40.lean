-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_LocalLatticeIndex_index_eq_det_dd433643ef40
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:09:47.616906+00:00
-- url     : https://prove2.me/submissions/102d8645-20a1-4177-9601-3df5ad9c6e54

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsLocalLatticeIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PLocalLatticeIndex
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_LocalLatticeIndex_norm_unit_16f7003adcaf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_LocalLatticeIndex_card_quot_span_bba263407b48
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_LocalLatticeIndex_isTorsionFree_1b49b6e7295e
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField IsDedekindDomain TensorProduct Module
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}
  {E : Type*} [AddCommGroup E] [Module (v.adicCompletion K) E]
  [Module (v.adicCompletionIntegers K) E]
  [IsScalarTower (v.adicCompletionIntegers K) (v.adicCompletion K) E]
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
namespace LocalLatticeIndex
theorem _root_.solution (A B : Submodule (v.adicCompletionIntegers K) E)
    (g : E ≃ₗ[v.adicCompletion K] E) (hfg : A.FG)
    (hsp : Submodule.span (v.adicCompletion K) (A : Set E) = ⊤)
    (hB : (B : Set E) = g '' A) (hBA : B ≤ A) :
    (B.toAddSubgroup.relIndex A.toAddSubgroup : ℝ) =
      ‖LinearMap.det (g : E →ₗ[v.adicCompletion K] E)‖⁻¹ := by
  classical
  have := LocalLatticeIndex.isTorsionFree A
  have : Module.Finite (v.adicCompletionIntegers K) A := Module.Finite.iff_fg.2 hfg
  set ι := Module.Free.ChooseBasisIndex (v.adicCompletionIntegers K) A
  let b := Module.Free.chooseBasis (v.adicCompletionIntegers K) A

  have hli : LinearIndependent (v.adicCompletion K) (fun i => (b i : E)) := by
    rw [← LinearIndependent.iff_fractionRing (v.adicCompletionIntegers K) (v.adicCompletion K)]
    exact b.linearIndependent.map' A.subtype (Submodule.ker_subtype A)
  have hspanR : Submodule.span (v.adicCompletionIntegers K) (Set.range fun i => (b i : E)) = A := by
    have : (Set.range fun i => (b i : E)) = A.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have hsp' : ⊤ ≤ Submodule.span (v.adicCompletion K) (Set.range fun i => (b i : E)) := by
    rw [← hsp]
    apply Submodule.span_le.2
    intro x hx
    have hx' : x ∈ Submodule.span (v.adicCompletionIntegers K) (Set.range fun i => (b i : E)) := by
      rw [hspanR]; exact hx
    exact Submodule.span_le_restrictScalars (v.adicCompletionIntegers K) (v.adicCompletion K) _ hx'
  let c : Basis ι (v.adicCompletion K) E := Basis.mk hli hsp'
  have hc : ∀ i, c i = (b i : E) := fun i => Basis.mk_apply hli hsp' i
  have hrepr : ∀ (x : A) (i : ι),
      c.repr (x : E) i = algebraMap _ (v.adicCompletion K) (b.repr x i) := by
    intro x i
    have hx : (x : E) = ∑ j, algebraMap _ (v.adicCompletion K) (b.repr x j) • c j := by
      calc (x : E) = ((∑ j, b.repr x j • b j : A) : E) := by rw [b.sum_repr]
        _ = ∑ j, algebraMap _ (v.adicCompletion K) (b.repr x j) • c j := by
          simp only [Submodule.coe_sum, Submodule.coe_smul, hc, algebraMap_smul]
    rw [hx, c.repr_sum_self]

  have hmaps : ∀ x ∈ A, (g.toLinearMap.restrictScalars (v.adicCompletionIntegers K)) x ∈ A := by
    intro x hx
    apply hBA
    show g x ∈ (B : Set E)
    rw [hB]
    exact ⟨x, hx, rfl⟩
  let φ : A →ₗ[v.adicCompletionIntegers K] A :=
    (g.toLinearMap.restrictScalars (v.adicCompletionIntegers K)).restrict hmaps
  have hφ : ∀ x : A, (φ x : E) = g x := fun x => rfl

  have hdet : LinearMap.det (g : E →ₗ[v.adicCompletion K] E) =
      algebraMap _ (v.adicCompletion K) (LinearMap.det φ) := by
    rw [← LinearMap.det_toMatrix c, ← LinearMap.det_toMatrix b, RingHom.map_det]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      LinearMap.toMatrix_apply, hc, LinearEquiv.coe_coe, ← hφ, hrepr]

  have hinj : Function.Injective φ := by
    intro x y h
    apply Subtype.ext
    apply g.injective
    rw [← hφ, ← hφ, h]
  have hrank : finrank _ (LinearMap.range φ) = finrank _ A := LinearMap.finrank_range_of_inj hinj
  set a := Submodule.smithNormalFormCoeffs b hrank
  let b' := Submodule.smithNormalFormTopBasis b hrank
  let ab := Submodule.smithNormalFormBotBasis b hrank
  have ha : ∀ i, a i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero b hrank

  have hcomap : Submodule.comap A.subtype B = LinearMap.range φ := by
    ext x
    simp only [Submodule.mem_comap, Submodule.coe_subtype, LinearMap.mem_range]
    constructor
    · intro hx
      have hx' : (x : E) ∈ (B : Set E) := hx
      rw [hB] at hx'
      obtain ⟨y, hy, hxy⟩ := hx'
      exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩
    · rintro ⟨y, rfl⟩
      show g y ∈ (B : Set E)
      rw [hB]
      exact ⟨y, y.2, rfl⟩
  have hidx : B.toAddSubgroup.relIndex A.toAddSubgroup = Nat.card (A ⧸ LinearMap.range φ) := by
    rw [← hcomap, AddSubgroup.relIndex, AddSubgroup.index_eq_card]
    rfl
  have hq : Nat.card (A ⧸ LinearMap.range φ) =
      ∏ i, Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span {a i}) := by
    rw [Nat.card_congr (Submodule.quotientEquivPiSpan (LinearMap.range φ) b hrank).toEquiv,
      Nat.card_pi]

  let w : Basis ι _ A := ab.map (LinearEquiv.ofInjective φ hinj).symm
  have hw : ∀ i, φ (w i) = a i • b' i := by
    intro i
    have h1 : φ (w i) = ((LinearEquiv.ofInjective φ hinj) (w i) : A) :=
      (LinearEquiv.ofInjective_apply _ _).symm
    rw [h1]
    simp only [w, Basis.map_apply, LinearEquiv.apply_symm_apply]
    exact Submodule.smithNormalFormBotBasis_def b hrank i
  have hdetprod : LinearMap.det φ * b'.det w = ∏ i, a i := by
    rw [← Basis.det_comp]
    have : (⇑φ ∘ ⇑w) = fun i => a i • b' i := funext hw
    rw [this, AlternatingMap.map_smul_univ, Basis.det_self, smul_eq_mul, mul_one]
  obtain ⟨u, hu⟩ := b'.isUnit_det w
  have hdetφ : LinearMap.det φ = (∏ i, a i) * ((u⁻¹ : (v.adicCompletionIntegers K)ˣ) :
      v.adicCompletionIntegers K) := by
    rw [← hdetprod, ← hu, mul_assoc, Units.mul_inv, mul_one]
  have hu1 : ‖algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
      ((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K)‖ = 1 :=
    LocalLatticeIndex.norm_unit v u⁻¹
  rw [hidx, hq, Nat.cast_prod, hdet, hdetφ, map_mul, map_prod, norm_mul, norm_prod, hu1, mul_one,
    ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun i _ => LocalLatticeIndex.card_quot_span v (ha i)
end LocalLatticeIndex
end GroundTheory.Heights₂.Heights.LatticeLemmas
