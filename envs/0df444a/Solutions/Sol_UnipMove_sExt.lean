-- Prove2me | solution 1 for UnipMove.sExt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:48:29.754021+00:00
-- url     : https://prove2.me/submissions/44ae02ad-9a86-416a-8791-f12f99df4662

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_KatoClassHeckeEulerFactorRelation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_HermSmulLeft
import Theorems.Thm_P2M_UnipMove_herm_smul_left__6f6c7a1bcd4e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UnipMove
open ReciprocityTheory.ChartRestriction.G.FD NumberField
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace UnipMove
theorem _root_.solution : SExt E := by
  intro r X ξ f hadd hsm
  classical
  have hsmul_mem : ∀ (α : 𝓞 E) (x : Fin r → E), x ∈ X.Λp ξ → (α : E) • x ∈ X.Λp ξ := by
    intro α x hx
    simp only [Data.Λp, AddSubgroup.mem_inf, Submodule.mem_toAddSubgroup, AddMonoidHom.mem_ker] at hx ⊢
    obtain ⟨h1, h2⟩ := hx
    refine ⟨?_, ?_⟩
    · have h3 := X.Λ.smul_mem α h1
      rwa [algebra_compatible_smul E α x] at h3
    · change herm X.Gm ((α : E) • x) ξ = 0
      change herm X.Gm x ξ = 0 at h2
      rw [herm_smul_left', h2, mul_zero]
  let N0 : Submodule (𝓞 E) (Fin r → E) :=
    { carrier := X.Λp ξ
      add_mem' := fun ha hb => (X.Λp ξ).add_mem ha hb
      zero_mem' := (X.Λp ξ).zero_mem
      smul_mem' := fun α x hx => by
        rw [algebra_compatible_smul E α x]
        exact hsmul_mem α x hx }
  let fL : N0 →ₗ[𝓞 E] E :=
    { toFun := fun x => f x
      map_add' := fun x y => hadd x x.2 y y.2
      map_smul' := fun α x => by
        change f (α • (x : Fin r → E)) = α • f x
        rw [algebra_compatible_smul E α (x : Fin r → E), hsm α x x.2, Algebra.smul_def] }
  obtain ⟨s, hsM, hspan, hli⟩ := exists_linearIndependent E (X.Λp ξ : Set (Fin r → E))
  have hli' : LinearIndepOn E id s := hli
  let B := Module.Basis.extend (K := E) (s := s) hli'
  let F : (Fin r → E) →ₗ[E] E := B.constr E (fun v => if (v : Fin r → E) ∈ s then f v else 0)
  have hFs : ∀ v ∈ s, F v = f v := by
    intro v hv
    have hv' : v ∈ LinearIndepOn.extend hli' (Set.subset_univ s) := Module.Basis.subset_extend hli' hv
    have h1 := B.constr_basis E (fun v => if (v : Fin r → E) ∈ s then f v else 0) ⟨v, hv'⟩
    have h2 : B ⟨v, hv'⟩ = v := by simp [B, Module.Basis.coe_extend]
    rw [h2] at h1
    change B.constr E (fun v => if (v : Fin r → E) ∈ s then f v else 0) v = f v
    rw [h1]
    simp [hv]
  refine ⟨F, fun μ hμ => ?_⟩
  have hμs : μ ∈ Submodule.span E s := by
    rw [hspan]
    exact Submodule.subset_span hμ
  obtain ⟨n, c, g, hsum⟩ := Submodule.mem_span_set'.1 hμs
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (𝓞 E)⁰ c
  have hd' : ∀ i, ∃ a : 𝓞 E, algebraMap (𝓞 E) E a = (d : 𝓞 E) • c i := fun i =>
    RingHom.mem_rangeS.1 (hd i)
  choose a ha using hd'
  have hgM : ∀ i, ((g i : Fin r → E)) ∈ X.Λp ξ := fun i => hsM (g i).2
  have hdE : algebraMap (𝓞 E) E (d : 𝓞 E) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
  have hFμ : F μ = ∑ i, c i * f (g i) := by
    rw [← hsum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hFs _ (g i).2, smul_eq_mul]
  have hdμ : algebraMap (𝓞 E) E (d : 𝓞 E) • μ = ∑ i, algebraMap (𝓞 E) E (a i) • (g i : Fin r → E) := by
    rw [← hsum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ha i, smul_smul, Algebra.smul_def (d : 𝓞 E) (c i)]
  have hmemd : algebraMap (𝓞 E) E (d : 𝓞 E) • μ ∈ N0 := hsmul_mem (d : 𝓞 E) μ hμ
  have hfd : f (algebraMap (𝓞 E) E (d : 𝓞 E) • μ) = ∑ i, algebraMap (𝓞 E) E (a i) * f (g i) := by
    have h1 : (⟨_, hmemd⟩ : N0) = ∑ i, a i • (⟨g i, hgM i⟩ : N0) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      rw [hdμ]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [algebra_compatible_smul E (a i)]
    have h2 := congrArg fL h1
    rw [map_sum] at h2
    change f _ = _ at h2
    rw [h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Algebra.smul_def]
    rfl
  have h3 : algebraMap (𝓞 E) E (d : 𝓞 E) * f μ = algebraMap (𝓞 E) E (d : 𝓞 E) * F μ := by
    rw [← hsm (d : 𝓞 E) μ hμ, hfd, hFμ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ha i, Algebra.smul_def, mul_assoc]
  exact (mul_left_cancel₀ hdE h3).symm
end UnipMove
