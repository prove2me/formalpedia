-- Prove2me | solution 1 for PDivisibleGroup.exists_mvFormalGroup_ker_eq_span_nthSeries_jointly_injective_surjective_of_isLocalRing_zmodp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/4c6c3c20-eb3e-5bd7-b96e-caa5b39e1a4b

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import Theorems.Thm_IsAdicComplete_of_module_finite_free_span_natCast
import Theorems.Thm_MvPowerSeries_mem_pow_span_X_of_coeff_eq_zero
import Theorems.Thm_MvFormalGroup_algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical
import Theorems.Thm_Algebra_TensorProduct_specialFibre_coordinates_sumElim_tmul
import Theorems.Thm_PDivisibleGroup_exists_surjective_mvPowerSeries_comp_eq_of_isLocalRing_zmodp
import Theorems.Thm_MvPowerSeries_isNoetherianRing_of_finite
import Theorems.Thm_PDivisibleGroup_Hopf_exists_forall_comp_transition_surjective_ker_eq_torsionIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_exists_mvFormalGroup_ker_eq_span_nthSeries_jointly_injective_surjective_of_isLocalRing_zmodp
p2m_attr_erase "instance" "MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra HopfAlgebra.IsHopfTower.refl"
p2m_attr_erase "simp" "CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul"

set_option autoImplicit false

universe u v w

open MvPowerSeries
open Function
open scoped TensorProduct

namespace CoordUp

section Reduction

variable (𝓞 : Type u) [CommRing 𝓞] (p : ℕ) [Algebra 𝓞 (ZMod p)] (T : Type v) [CommRing T] [Algebra 𝓞 T]

private noncomputable abbrev red : T →ₐ[𝓞] ZMod p ⊗[𝓞] T := Algebra.TensorProduct.includeRight

variable {𝓞 p T}

private theorem red_apply (a : T) : red 𝓞 p T a = (1 : ZMod p) ⊗ₜ[𝓞] a := rfl

private theorem red_surjective (hk : Surjective (algebraMap 𝓞 (ZMod p))) :
    Surjective (red 𝓞 p T) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul c a =>
    obtain ⟨o, rfl⟩ := hk c
    refine ⟨o • a, ?_⟩
    rw [red_apply, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.algebraMap_eq_smul_one]
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩

private theorem natCast_eq_zero : (p : ZMod p ⊗[𝓞] T) = 0 := by
  rw [Algebra.TensorProduct.natCast_def, ZMod.natCast_self, TensorProduct.zero_tmul]

private theorem red_natCast_mul (a : T) : red 𝓞 p T ((p : T) * a) = 0 := by
  rw [map_mul, map_natCast, natCast_eq_zero, zero_mul]

private theorem ker_red (hk : Surjective (algebraMap 𝓞 (ZMod p)))
    (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)}) :
    RingHom.ker (red 𝓞 p T : T →ₐ[𝓞] ZMod p ⊗[𝓞] T) = Ideal.span {(p : T)} := by
  apply le_antisymm
  ·
    set J : Ideal T := Ideal.span {(p : T)} with hJ
    have hle : RingHom.ker (algebraMap 𝓞 (ZMod p)) ≤
        RingHom.ker ((Ideal.Quotient.mk J).comp (algebraMap 𝓞 T)) := by
      intro o ho
      rw [hker] at ho
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ho
      rw [RingHom.mem_ker, RingHom.comp_apply, map_mul, map_natCast, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    let κ₀ : ZMod p →+* T ⧸ J := (algebraMap 𝓞 (ZMod p)).liftOfSurjective hk ⟨_, hle⟩
    have hκ₀ : ∀ o, κ₀ (algebraMap 𝓞 (ZMod p) o) = Ideal.Quotient.mk J (algebraMap 𝓞 T o) := fun o =>
      (algebraMap 𝓞 (ZMod p)).liftOfRightInverse_comp_apply _ _ ⟨_, hle⟩ o
    let κ : ZMod p →ₐ[𝓞] T ⧸ J := { κ₀ with commutes' := fun o => (hκ₀ o).trans rfl }
    let Ψ : ZMod p ⊗[𝓞] T →ₐ[𝓞] T ⧸ J :=
      Algebra.TensorProduct.lift κ (Ideal.Quotient.mkₐ 𝓞 J) fun _ _ => Commute.all _ _
    intro a ha
    rw [RingHom.mem_ker] at ha
    have h1 : Ψ (red 𝓞 p T a) = Ideal.Quotient.mk J a := by
      rw [red_apply, Algebra.TensorProduct.lift_tmul, map_one, one_mul]; rfl
    rw [show red 𝓞 p T a = 0 from ha, map_zero] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.1 h1.symm
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    have := red_natCast_mul (𝓞 := 𝓞) (p := p) (1 : T)
    rwa [mul_one] at this

private theorem red_eq_red_iff (hk : Surjective (algebraMap 𝓞 (ZMod p)))
    (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)}) (a b : T) :
    red 𝓞 p T a = red 𝓞 p T b ↔ a - b ∈ Ideal.span {(p : T)} := by
  rw [← ker_red hk hker, RingHom.mem_ker, map_sub, sub_eq_zero]

end Reduction

section Nilp

variable {𝓞 : Type u} [CommRing 𝓞] {p : ℕ} [Fact p.Prime] [Algebra 𝓞 (ZMod p)]
  {T : Type v} [CommRing T] [HopfAlgebra 𝓞 T] [Module.Free 𝓞 T] [Module.Finite 𝓞 T]

omit [Module.Finite 𝓞 T] in

private theorem isLocalRing_fibre (hk : Surjective (algebraMap 𝓞 (ZMod p))) [IsLocalRing T] :
    IsLocalRing (ZMod p ⊗[𝓞] T) := by
  haveI : Module.FaithfullyFlat 𝓞 T := inferInstance
  haveI : Nontrivial (ZMod p ⊗[𝓞] T) := inferInstance
  exact IsLocalRing.of_surjective' (red 𝓞 p T).toRingHom (red_surjective hk)

private theorem isNilpotent_of_counit_eq_zero (hk : Surjective (algebraMap 𝓞 (ZMod p))) [IsLocalRing T]
    {b : ZMod p ⊗[𝓞] T} (hb : Coalgebra.counit (R := ZMod p) b = 0) : IsNilpotent b := by
  haveI := isLocalRing_fibre (T := T) hk
  haveI : IsArtinianRing (ZMod p ⊗[𝓞] T) := IsArtinianRing.of_finite (ZMod p) _
  have hmem : b ∈ IsLocalRing.maximalIdeal (ZMod p ⊗[𝓞] T) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := hu.map (Bialgebra.counitAlgHom (ZMod p) (ZMod p ⊗[𝓞] T))
    rw [Bialgebra.counitAlgHom_apply, hb] at this
    exact not_isUnit_zero this
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := ZMod p ⊗[𝓞] T)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hn
  refine ⟨n, ?_⟩
  have : b ^ n ∈ IsLocalRing.maximalIdeal (ZMod p ⊗[𝓞] T) ^ n := Ideal.pow_mem_pow hmem n
  rw [hn] at this
  exact (Submodule.mem_bot _).1 this

private theorem mem_radical_of_counit_red_eq_zero (hk : Surjective (algebraMap 𝓞 (ZMod p)))
    (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)}) [IsLocalRing T]
    {a : T} (ha : Coalgebra.counit (R := ZMod p) (red 𝓞 p T a) = 0) :
    a ∈ (Ideal.span {(p : T)}).radical := by
  obtain ⟨n, hn⟩ := isNilpotent_of_counit_eq_zero (T := T) hk ha
  refine ⟨n, ?_⟩
  rw [← ker_red hk hker, RingHom.mem_ker, map_pow]
  exact hn

end Nilp

section Eval

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
  (R₀ : ℕ → Type v) [∀ v, CommRing (R₀ v)] [∀ v, Algebra 𝓞 (R₀ v)]
  [∀ v, Module.Free 𝓞 (R₀ v)] [∀ v, Module.Finite 𝓞 (R₀ v)]
  {σ : Type w} [Finite σ] (x : ∀ v, σ → R₀ v)
  (hxr : ∀ v i, x v i ∈ (Ideal.span {(p : R₀ v)}).radical)

variable (𝓞) in

private noncomputable def evalAt (v : ℕ) : MvPowerSeries σ 𝓞 →ₐ[𝓞] R₀ v :=
  haveI : IsAdicComplete (Ideal.span {(p : R₀ v)}) (R₀ v) :=
    IsAdicComplete.of_module_finite_free_span_natCast (𝓞 := 𝓞) p (R₀ v)
  MvFormalGroup.adicEvalAlgHom (R := 𝓞) (Ideal.span {(p : R₀ v)}) (hxr v)

private theorem evalAt_apply (v : ℕ) (G : MvPowerSeries σ 𝓞) :
    evalAt 𝓞 p R₀ x hxr v G = MvFormalGroup.adicEval (Ideal.span {(p : R₀ v)}) (x v) G := by
  haveI : IsAdicComplete (Ideal.span {(p : R₀ v)}) (R₀ v) :=
    IsAdicComplete.of_module_finite_free_span_natCast (𝓞 := 𝓞) p (R₀ v)
  exact congrFun (MvFormalGroup.coe_adicEvalAlgHom (R := 𝓞) (Ideal.span {(p : R₀ v)}) (hxr v)) G

private theorem evalAt_X (v : ℕ) (i : σ) :
    evalAt 𝓞 p R₀ x hxr v (X i : MvPowerSeries σ 𝓞) = x v i := by
  rw [evalAt_apply, MvFormalGroup.adicEval_X]

private theorem evalAt_coe (v : ℕ) (P : MvPolynomial σ 𝓞) :
    evalAt 𝓞 p R₀ x hxr v (P : MvPowerSeries σ 𝓞) = MvPolynomial.aeval (x v) P := by
  rw [evalAt_apply, MvFormalGroup.adicEval_coe]

private theorem comp_evalAt (t : ∀ v, R₀ (v + 1) →ₐ[𝓞] R₀ v) (hxt : ∀ v i, t v (x (v + 1) i) = x v i)
    (v : ℕ) : (t v).comp (evalAt 𝓞 p R₀ x hxr (v + 1)) = evalAt 𝓞 p R₀ x hxr v := by
  haveI : IsAdicComplete (Ideal.span {(p : R₀ v)}) (R₀ v) :=
    IsAdicComplete.of_module_finite_free_span_natCast (𝓞 := 𝓞) p (R₀ v)
  haveI : IsAdicComplete (Ideal.span {(p : R₀ (v + 1))}) (R₀ (v + 1)) :=
    IsAdicComplete.of_module_finite_free_span_natCast (𝓞 := 𝓞) p (R₀ (v + 1))
  apply AlgHom.ext
  intro G
  rw [AlgHom.comp_apply, evalAt_apply, evalAt_apply,
    MvFormalGroup.map_adicEval (R := 𝓞) (Ideal.span {(p : R₀ (v + 1))}) (Ideal.span {(p : R₀ v)})
      (t v) (Submodule.fg_span_singleton _) ?_ (hxr (v + 1)) G]
  · congr 1
    funext i
    exact hxt v i
  · intro s hs
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hs
    refine Ideal.le_radical ?_
    rw [map_mul, map_natCast]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

end Eval

section Surj

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] [Algebra 𝓞 (ZMod p)]
  [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
  (R₀ : ℕ → Type v) [∀ v, CommRing (R₀ v)] [∀ v, Algebra 𝓞 (R₀ v)]
  [∀ v, Module.Free 𝓞 (R₀ v)] [∀ v, Module.Finite 𝓞 (R₀ v)]
  {σ : Type w} [Finite σ] (x : ∀ v, σ → R₀ v)
  (hxr : ∀ v i, x v i ∈ (Ideal.span {(p : R₀ v)}).radical)
  (πbar : ∀ v, MvPolynomial σ (ZMod p) →ₐ[ZMod p] ZMod p ⊗[𝓞] R₀ v)
  (hxred : ∀ v i, red 𝓞 p (R₀ v) (x v i) = πbar v (MvPolynomial.X i))

include hxred in

private theorem red_evalAt_coe (v : ℕ) (P : MvPolynomial σ 𝓞) :
    red 𝓞 p (R₀ v) (evalAt 𝓞 p R₀ x hxr v (P : MvPowerSeries σ 𝓞)) =
      πbar v (MvPolynomial.map (algebraMap 𝓞 (ZMod p)) P) := by
  rw [evalAt_coe, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  have hπ : πbar v = MvPolynomial.aeval (fun i => πbar v (MvPolynomial.X i)) :=
    MvPolynomial.algHom_ext fun i =>
      (MvPolynomial.aeval_X (fun i => πbar v (MvPolynomial.X i)) i).symm
  rw [hπ, MvPolynomial.aeval_map_algebraMap]
  congr 2
  funext i
  exact hxred v i

end Surj

section SurjInj

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] [Algebra 𝓞 (ZMod p)]
  [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
  (R₀ : ℕ → Type v) [∀ v, CommRing (R₀ v)] [∀ v, Algebra 𝓞 (R₀ v)]
  [∀ v, Module.Free 𝓞 (R₀ v)] [∀ v, Module.Finite 𝓞 (R₀ v)]
  {σ : Type w} [Finite σ] (x : ∀ v, σ → R₀ v)
  (hxr : ∀ v i, x v i ∈ (Ideal.span {(p : R₀ v)}).radical)
  (πbar : ∀ v, MvPolynomial σ (ZMod p) →ₐ[ZMod p] ZMod p ⊗[𝓞] R₀ v)
  (hxred : ∀ v i, red 𝓞 p (R₀ v) (x v i) = πbar v (MvPolynomial.X i))
  (hk : Surjective (algebraMap 𝓞 (ZMod p)))
  (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
  (hπs : ∀ v, Surjective (πbar v))

include hxred hk hker hπs in

private theorem evalAt_surjective (v : ℕ) : Surjective (evalAt 𝓞 p R₀ x hxr v) := by
  let N : Submodule 𝓞 (R₀ v) := LinearMap.range (evalAt 𝓞 p R₀ x hxr v).toLinearMap
  have hN : (⊤ : Submodule 𝓞 (R₀ v)) ≤ N := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := Ideal.span {(p : 𝓞)}) Module.Finite.fg_top
      (IsAdicComplete.le_jacobson_bot _) ?_
    intro m _
    obtain ⟨Q, hQ⟩ := hπs v (red 𝓞 p (R₀ v) m)
    obtain ⟨P, rfl⟩ := MvPolynomial.map_surjective (algebraMap 𝓞 (ZMod p)) hk Q
    have hdiff : m - evalAt 𝓞 p R₀ x hxr v ↑P ∈ Ideal.span {(p : R₀ v)} := by
      rw [← red_eq_red_iff hk hker, red_evalAt_coe p R₀ x hxr πbar hxred, hQ]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hdiff
    have hm : m = evalAt 𝓞 p R₀ x hxr v ↑P + (p : 𝓞) • c := by
      rw [Algebra.smul_def, map_natCast]
      linear_combination (-1 : R₀ v) * hc
    rw [hm]
    exact Submodule.add_mem_sup ⟨_, rfl⟩
      (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top)
  intro m
  obtain ⟨G, hG⟩ := hN (Submodule.mem_top (x := m))
  exact ⟨G, hG⟩

omit [Fact p.Prime] in

private theorem coeff_eq_zero_of_mem_pow_span_X {k : Type*} [CommRing k] {σ : Type*} :
    ∀ (K : ℕ) {φ : MvPolynomial σ k},
      φ ∈ Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ k)) ^ K →
      ∀ m : σ →₀ ℕ, m.degree < K → MvPolynomial.coeff m φ = 0
  | 0, _, _, _, hm => absurd hm (Nat.not_lt_zero _)
  | K + 1, φ, hφ, m₀, hm₀ => by
    classical
    rw [pow_succ] at hφ
    refine Submodule.smul_induction_on
      (p := fun ψ => ∀ m : σ →₀ ℕ, m.degree < K + 1 → MvPolynomial.coeff m ψ = 0) hφ ?_ ?_ m₀ hm₀
    · intro a ha b hb m hm
      rw [smul_eq_mul, MvPolynomial.coeff_mul]
      apply Finset.sum_eq_zero
      rintro ⟨m₁, m₂⟩ hmm
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hmm
      by_cases h₁ : m₁.degree < K
      · rw [coeff_eq_zero_of_mem_pow_span_X K ha m₁ h₁, zero_mul]
      ·
        have hdeg : m₁.degree + m₂.degree = m.degree := by rw [← map_add, hmm]
        have h₂ : m₂ = 0 := (Finsupp.degree_eq_zero_iff _).1 (by omega)
        subst h₂
        have hb0 : MvPolynomial.coeff 0 b = 0 := by
          rw [← Set.image_univ] at hb
          rw [← MvPolynomial.notMem_support_iff]
          intro h0
          obtain ⟨i, -, hi⟩ := (MvPolynomial.mem_ideal_span_X_image.1 hb) 0 h0
          exact hi rfl
        rw [hb0, mul_zero]
    · intro a b ha hb m hm
      rw [MvPolynomial.coeff_add, ha m hm, hb m hm, add_zero]

include hxred hker hπs in

private theorem coeff_mem_span_of_evalAt_eq_zero {K : ℕ} {v : ℕ}
    (hv : RingHom.ker (πbar v) ≤
      Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ (ZMod p))) ^ K)
    {G : MvPowerSeries σ 𝓞} (hG : evalAt 𝓞 p R₀ x hxr v G = 0)
    (m : σ →₀ ℕ) (hm : m.degree < K) : MvPowerSeries.coeff m G ∈ Ideal.span {(p : 𝓞)} := by
  classical

  set box : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => K with hbox
  set P : MvPolynomial σ 𝓞 := MvPowerSeries.trunc' 𝓞 box G with hP
  set H : MvPowerSeries σ 𝓞 := G - ↑P with hH
  have hmbox : ∀ m' : σ →₀ ℕ, m'.degree < K → m' ≤ box := by
    intro m' hm' i
    rw [hbox, Finsupp.coe_equivFunOnFinite_symm]
    exact (Finsupp.le_degree i m').trans hm'.le
  have hHcoeff : ∀ m' : σ →₀ ℕ, m'.degree < K → MvPowerSeries.coeff m' H = 0 := by
    intro m' hm'
    rw [hH, map_sub, MvPolynomial.coeff_coe, hP, MvPowerSeries.coeff_trunc', if_pos (hmbox m' hm'),
      sub_self]

  have hHmem := MvPowerSeries.mem_pow_span_X_of_coeff_eq_zero K H hHcoeff
  set 𝔛 : Ideal (MvPowerSeries σ 𝓞) :=
    Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ 𝓞)) with h𝔛
  set 𝔛ₚ : Ideal (MvPolynomial σ (ZMod p)) :=
    Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ (ZMod p))) with h𝔛ₚ
  have hπH : evalAt 𝓞 p R₀ x hxr v H ∈ (Ideal.span (Set.range (x v))) ^ K := by
    have h1 : evalAt 𝓞 p R₀ x hxr v H ∈ Ideal.map (evalAt 𝓞 p R₀ x hxr v) (𝔛 ^ K) :=
      Ideal.mem_map_of_mem _ hHmem
    rw [Ideal.map_pow, h𝔛, Ideal.map_span, ← Set.range_comp] at h1
    have hcomp : (⇑(evalAt 𝓞 p R₀ x hxr v) ∘ (MvPowerSeries.X : σ → MvPowerSeries σ 𝓞)) = x v :=
      funext fun i => evalAt_X p R₀ x hxr v i
    rwa [hcomp] at h1

  have hred : red 𝓞 p (R₀ v) (evalAt 𝓞 p R₀ x hxr v ↑P) ∈ Ideal.map (πbar v) (𝔛ₚ ^ K) := by
    have hPH : evalAt 𝓞 p R₀ x hxr v ↑P = - evalAt 𝓞 p R₀ x hxr v H := by
      rw [hH, map_sub, hG, zero_sub, neg_neg]
    rw [hPH, map_neg, Ideal.neg_mem_iff]
    have h2 : red 𝓞 p (R₀ v) (evalAt 𝓞 p R₀ x hxr v H) ∈
        Ideal.map (red 𝓞 p (R₀ v)) ((Ideal.span (Set.range (x v))) ^ K) := Ideal.mem_map_of_mem _ hπH
    rw [Ideal.map_pow, Ideal.map_span, ← Set.range_comp] at h2
    rw [Ideal.map_pow, h𝔛ₚ, Ideal.map_span, ← Set.range_comp]
    have hcomp : (⇑(red 𝓞 p (R₀ v)) ∘ x v) =
        (⇑(πbar v) ∘ (MvPolynomial.X : σ → MvPolynomial σ (ZMod p))) :=
      funext fun i => hxred v i
    rwa [hcomp] at h2
  rw [red_evalAt_coe p R₀ x hxr πbar hxred] at hred

  have hPbar : MvPolynomial.map (algebraMap 𝓞 (ZMod p)) P ∈ 𝔛ₚ ^ K := by
    have h3 := Ideal.mem_comap.2 hred
    rw [Ideal.comap_map_of_surjective _ (hπs v)] at h3
    have h4 : 𝔛ₚ ^ K ⊔ Ideal.comap (πbar v) ⊥ ≤ 𝔛ₚ ^ K := sup_le le_rfl hv
    exact h4 h3

  have h5 := coeff_eq_zero_of_mem_pow_span_X K hPbar m hm
  rw [MvPolynomial.coeff_map, ← RingHom.mem_ker, hker] at h5
  have h6 : MvPolynomial.coeff m P = MvPowerSeries.coeff m G := by
    rw [hP, MvPowerSeries.coeff_trunc', if_pos (hmbox m hm)]
  rwa [h6] at h5

end SurjInj

section Trunc

variable {R : Type*} [CommRing R] {σ : Type w} [Finite σ]

private noncomputable def truncDeg (K : ℕ) (φ : MvPowerSeries σ R) : MvPolynomial σ R :=
  ∑ m ∈ (Finsupp.finite_of_degree_lt (σ := σ) K).toFinset,
    MvPolynomial.monomial m (MvPowerSeries.coeff m φ)

private theorem coeff_truncDeg (K : ℕ) (φ : MvPowerSeries σ R) (m : σ →₀ ℕ) :
    MvPolynomial.coeff m (truncDeg K φ) = if m.degree < K then MvPowerSeries.coeff m φ else 0 := by
  classical
  rw [truncDeg, MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]

private theorem coeff_sub_truncDeg (K : ℕ) (φ : MvPowerSeries σ R) (m : σ →₀ ℕ)
    (hm : m.degree < K) :
    MvPowerSeries.coeff m (φ - (truncDeg K φ : MvPowerSeries σ R)) = 0 := by
  rw [map_sub, MvPolynomial.coeff_coe, coeff_truncDeg, if_pos hm, sub_self]

private theorem sub_truncDeg_mem (K : ℕ) (φ : MvPowerSeries σ R) :
    φ - (truncDeg K φ : MvPowerSeries σ R) ∈
      Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) ^ K :=
  MvPowerSeries.mem_pow_span_X_of_coeff_eq_zero K _ (coeff_sub_truncDeg K φ)

end Trunc

section Prelim

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Algebra 𝓞 (ZMod p)]
  (R₀ : ℕ → Type v) [∀ v, CommRing (R₀ v)] [∀ v, Algebra 𝓞 (R₀ v)]

private theorem ker_anti (t : ∀ v, R₀ (v + 1) →ₐ[𝓞] R₀ v) {σ : Type w} [Finite σ]
    (πbar : ∀ v, MvPolynomial σ (ZMod p) →ₐ[ZMod p] ZMod p ⊗[𝓞] R₀ v)
    (hπc : ∀ v (P : MvPolynomial σ (ZMod p)),
      Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (t v) (πbar (v + 1) P) = πbar v P)
    {v w : ℕ} (h : v ≤ w) : RingHom.ker (πbar w) ≤ RingHom.ker (πbar v) := by
  induction h with
  | refl => exact le_rfl
  | @step w _ ih =>
    refine le_trans ?_ ih
    intro P hP
    rw [RingHom.mem_ker] at hP ⊢
    rw [← hπc w P, hP, map_zero]

private theorem exists_pow_span_red_eq_bot {σ : Type w} [Finite σ] (x : ∀ v, σ → R₀ v)
    (hxr : ∀ v i, x v i ∈ (Ideal.span {(p : R₀ v)}).radical) (v : ℕ) :
    ∃ M : ℕ, Ideal.span (Set.range fun i => red 𝓞 p (R₀ v) (x v i)) ^ M = ⊥ := by
  have hfg : (Ideal.span (Set.range fun i => red 𝓞 p (R₀ v) (x v i))).FG :=
    ⟨(Set.finite_range _).toFinset, by rw [Set.Finite.coe_toFinset]⟩
  have hnil : IsNilpotent (Ideal.span (Set.range fun i => red 𝓞 p (R₀ v) (x v i))) := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical hfg, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨n, hn⟩ := hxr v i
    refine ⟨n, ?_⟩
    rw [← map_pow]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hn
    rw [← hc, map_mul, map_natCast, natCast_eq_zero, mul_zero]
    exact Ideal.zero_mem _
  obtain ⟨M, hM⟩ := hnil
  exact ⟨M, hM⟩

end Prelim

section JSurj

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] [Algebra 𝓞 (ZMod p)]
  [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
  (R₀ : ℕ → Type v) [∀ v, CommRing (R₀ v)] [∀ v, Algebra 𝓞 (R₀ v)]
  [∀ v, Module.Free 𝓞 (R₀ v)] [∀ v, Module.Finite 𝓞 (R₀ v)]
  (t : ∀ v, R₀ (v + 1) →ₐ[𝓞] R₀ v)
  {σ : Type w} [Finite σ] (x : ∀ v, σ → R₀ v)
  (hxr : ∀ v i, x v i ∈ (Ideal.span {(p : R₀ v)}).radical)
  (hxt : ∀ v i, t v (x (v + 1) i) = x v i)
  (πbar : ∀ v, MvPolynomial σ (ZMod p) →ₐ[ZMod p] ZMod p ⊗[𝓞] R₀ v)
  (hxred : ∀ v i, red 𝓞 p (R₀ v) (x v i) = πbar v (MvPolynomial.X i))
  (hπc : ∀ v (P : MvPolynomial σ (ZMod p)),
    Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (t v) (πbar (v + 1) P) = πbar v P)
  (hk : Surjective (algebraMap 𝓞 (ZMod p)))
  (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
  (hπs : ∀ v, Surjective (πbar v))
  (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
  (hπk : ∀ N : ℕ, ∃ v, RingHom.ker (πbar v) ≤
    Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ (ZMod p))) ^ N)

include hxred hπc hk hker hπs hπk hxr in

private theorem exists_sub_evalAt_mem (z : ∀ v, R₀ v) (hz : ∀ v, t v (z (v + 1)) = z v) :
    ∃ G₀ : MvPowerSeries σ 𝓞, ∀ v, z v - evalAt 𝓞 p R₀ x hxr v G₀ ∈ Ideal.span {(p : R₀ v)} := by
  classical

  have hP : ∀ v, ∃ P : MvPolynomial σ 𝓞,
      πbar v (MvPolynomial.map (algebraMap 𝓞 (ZMod p)) P) = red 𝓞 p (R₀ v) (z v) := by
    intro v
    obtain ⟨Q, hQ⟩ := hπs v (red 𝓞 p (R₀ v) (z v))
    obtain ⟨P, rfl⟩ := MvPolynomial.map_surjective (algebraMap 𝓞 (ZMod p)) hk Q
    exact ⟨P, hQ⟩
  choose P hP using hP
  set Pb : ∀ v, MvPolynomial σ (ZMod p) := fun v => MvPolynomial.map (algebraMap 𝓞 (ZMod p)) (P v)
    with hPb

  have htel : ∀ {v w : ℕ}, v ≤ w → Pb w - Pb v ∈ RingHom.ker (πbar v) := by
    intro v w h
    induction h with
    | refl => rw [sub_self]; exact zero_mem _
    | @step w hvw ih =>
      have h1 : Pb (w + 1) - Pb w ∈ RingHom.ker (πbar w) := by
        rw [RingHom.mem_ker, map_sub, sub_eq_zero, ← hπc w, hPb]
        simp only
        rw [hP (w + 1), hP w, red_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hz w, red_apply]
      have : Pb (w + 1) - Pb v = (Pb (w + 1) - Pb w) + (Pb w - Pb v) := by ring
      rw [this]
      exact add_mem (ker_anti p R₀ t πbar hπc hvw h1) ih

  let v₀ : ℕ → ℕ := fun N => Nat.find (hπk N)
  have hv₀ : ∀ N, RingHom.ker (πbar (v₀ N)) ≤
      Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ (ZMod p))) ^ N :=
    fun N => Nat.find_spec (hπk N)
  have hv₀mono : ∀ {N N' : ℕ}, N ≤ N' → v₀ N ≤ v₀ N' := by
    intro N N' h
    exact Nat.find_mono (fun v hv => hv.trans (Ideal.pow_le_pow_right h))

  let Gb : MvPowerSeries σ (ZMod p) := fun m => MvPolynomial.coeff m (Pb (v₀ (m.degree + 1)))
  have hGb : ∀ (K w : ℕ), v₀ K ≤ w → ∀ m : σ →₀ ℕ, m.degree < K →
      MvPolynomial.coeff m (Pb w) = Gb m := by
    intro K w hw m hm
    have hu : v₀ (m.degree + 1) ≤ w := (hv₀mono hm).trans hw
    have hdiff := htel hu
    have hzero := coeff_eq_zero_of_mem_pow_span_X (m.degree + 1)
      ((hv₀ (m.degree + 1)) hdiff) m (Nat.lt_succ_self _)
    rw [MvPolynomial.coeff_sub, sub_eq_zero] at hzero
    exact hzero
  choose g hg using fun m => hk (Gb m)
  let G₀ : MvPowerSeries σ 𝓞 := g
  refine ⟨G₀, fun v => ?_⟩

  obtain ⟨K, hK⟩ := exists_pow_span_red_eq_bot (𝓞 := 𝓞) p R₀ x hxr v
  set w := max v (v₀ K) with hw
  have h1 : z v - evalAt 𝓞 p R₀ x hxr v ↑(P w) ∈ Ideal.span {(p : R₀ v)} := by
    rw [← red_eq_red_iff hk hker, red_evalAt_coe p R₀ x hxr πbar hxred]
    have := htel (le_max_left v (v₀ K))
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at this
    change red 𝓞 p (R₀ v) (z v) = πbar v (Pb w)
    rw [this, hP v]
  have h2 : evalAt 𝓞 p R₀ x hxr v ↑(P w) - evalAt 𝓞 p R₀ x hxr v G₀ ∈ Ideal.span {(p : R₀ v)} := by
    rw [← red_eq_red_iff hk hker, eq_comm, ← sub_eq_zero, ← map_sub, ← map_sub]
    set D : MvPowerSeries σ 𝓞 := G₀ - ↑(P w) with hD
    have hsplit : D = (truncDeg K D : MvPowerSeries σ 𝓞) + (D - (truncDeg K D : MvPowerSeries σ 𝓞)) := by ring
    rw [hsplit, map_add, map_add]

    have hlow : red 𝓞 p (R₀ v) (evalAt 𝓞 p R₀ x hxr v (truncDeg K D : MvPowerSeries σ 𝓞)) = 0 := by
      rw [red_evalAt_coe p R₀ x hxr πbar hxred]
      have : MvPolynomial.map (algebraMap 𝓞 (ZMod p)) (truncDeg K D) = 0 := by
        ext m
        rw [MvPolynomial.coeff_map, coeff_truncDeg, MvPolynomial.coeff_zero]
        split_ifs with hm
        · rw [hD, map_sub, MvPolynomial.coeff_coe, map_sub, show MvPowerSeries.coeff m G₀ = g m from rfl,
            hg m, ← hGb K w (le_max_right _ _) m hm, hPb]
          simp only
          rw [MvPolynomial.coeff_map, sub_self]
        · rw [map_zero]
      rw [this, map_zero]

    have hhigh : red 𝓞 p (R₀ v) (evalAt 𝓞 p R₀ x hxr v (D - (truncDeg K D : MvPowerSeries σ 𝓞))) = 0 := by
      have hmem : evalAt 𝓞 p R₀ x hxr v (D - (truncDeg K D : MvPowerSeries σ 𝓞)) ∈ (Ideal.span (Set.range (x v))) ^ K := by
        have h1 := Ideal.mem_map_of_mem (evalAt 𝓞 p R₀ x hxr v) (sub_truncDeg_mem K D)
        rw [Ideal.map_pow, Ideal.map_span, ← Set.range_comp] at h1
        have hcomp : (⇑(evalAt 𝓞 p R₀ x hxr v) ∘
            (MvPowerSeries.X : σ → MvPowerSeries σ 𝓞)) = x v :=
          funext fun i => evalAt_X p R₀ x hxr v i
        rwa [hcomp] at h1
      have h2 := Ideal.mem_map_of_mem (red 𝓞 p (R₀ v)) hmem
      rw [Ideal.map_pow, Ideal.map_span, ← Set.range_comp] at h2
      have hcomp2 : (⇑(red 𝓞 p (R₀ v)) ∘ x v) = fun i => red 𝓞 p (R₀ v) (x v i) := rfl
      rw [hcomp2, hK] at h2
      exact (Submodule.mem_bot _).1 h2
    rw [hlow, hhigh, add_zero]
  have := add_mem h1 h2
  rwa [sub_add_sub_cancel] at this

end JSurj

section CharP

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] [Algebra 𝓞 (ZMod p)]
  [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
  (R₀ : ℕ → Type v) [∀ v, CommRing (R₀ v)] [∀ v, Algebra 𝓞 (R₀ v)]
  [∀ v, Module.Free 𝓞 (R₀ v)] [∀ v, Module.Finite 𝓞 (R₀ v)]
  (t : ∀ v, R₀ (v + 1) →ₐ[𝓞] R₀ v)
  {σ : Type w} [Finite σ] (x : ∀ v, σ → R₀ v)
  (hxr : ∀ v i, x v i ∈ (Ideal.span {(p : R₀ v)}).radical)
  (hxt : ∀ v i, t v (x (v + 1) i) = x v i)
  (πbar : ∀ v, MvPolynomial σ (ZMod p) →ₐ[ZMod p] ZMod p ⊗[𝓞] R₀ v)
  (hxred : ∀ v i, red 𝓞 p (R₀ v) (x v i) = πbar v (MvPolynomial.X i))
  (hπc : ∀ v (P : MvPolynomial σ (ZMod p)),
    Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (t v) (πbar (v + 1) P) = πbar v P)
  (hk : Surjective (algebraMap 𝓞 (ZMod p)))
  (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
  (hπs : ∀ v, Surjective (πbar v))
  (hp0 : (p : 𝓞) = 0)
  (hπk : ∀ N : ℕ, ∃ v, RingHom.ker (πbar v) ≤
    Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ (ZMod p))) ^ N)

include hxred hker hπs hπk hp0 in

private theorem eq_zero_of_forall_evalAt_eq_zero {G : MvPowerSeries σ 𝓞}
    (hG : ∀ v, evalAt 𝓞 p R₀ x hxr v G = 0) : G = 0 := by
  ext m
  rw [map_zero]
  obtain ⟨v, hv⟩ := hπk (m.degree + 1)
  have h := coeff_mem_span_of_evalAt_eq_zero p R₀ x hxr πbar hxred hker hπs hv (hG v) m (Nat.lt_succ_self _)
  rwa [hp0, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot] at h

include hxred hπc hk hker hπs hπk hxr hp0 in

private theorem exists_forall_evalAt_eq (z : ∀ v, R₀ v) (hz : ∀ v, t v (z (v + 1)) = z v) :
    ∃ G : MvPowerSeries σ 𝓞, ∀ v, evalAt 𝓞 p R₀ x hxr v G = z v := by
  obtain ⟨G₀, hG₀⟩ := exists_sub_evalAt_mem p R₀ t x hxr πbar hxred hπc hk hker hπs hπk z hz
  refine ⟨G₀, fun v => ?_⟩
  have h := hG₀ v
  have hpv : (p : R₀ v) = 0 := by rw [← map_natCast (algebraMap 𝓞 (R₀ v)), hp0, map_zero]
  rw [hpv, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot, sub_eq_zero] at h
  exact h.symm

end CharP

end CoordUp

theorem CoordUp.Up
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp0 : (p : 𝓞) = 0)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (R₀ : ℕ → Type v) [∀ v, CommRing (R₀ v)] [∀ v, Algebra 𝓞 (R₀ v)]
    [∀ v, Module.Free 𝓞 (R₀ v)] [∀ v, Module.Finite 𝓞 (R₀ v)]
    (t₀ : ∀ v, R₀ (v + 1) →ₐ[𝓞] R₀ v)
    {σ : Type w} [Finite σ] (x : ∀ v, σ → R₀ v) (hxt : ∀ v i, t₀ v (x (v + 1) i) = x v i)
    (hxrad : ∀ v i, x v i ∈ (Ideal.span {(p : R₀ v)}).radical)
    (hxsurj : ∀ v, Function.Surjective
      (MvPolynomial.aeval (fun i => (1 : ZMod p) ⊗ₜ[𝓞] x v i) :
        MvPolynomial σ (ZMod p) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) (R₀ v)))
    (hxker : ∀ N : ℕ, ∃ v, RingHom.ker
      (MvPolynomial.aeval (fun i => (1 : ZMod p) ⊗ₜ[𝓞] x v i) :
        MvPolynomial σ (ZMod p) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) (R₀ v)) ≤
      (Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ (ZMod p)))) ^ N) :
    ∃ π : ∀ v, MvPowerSeries σ 𝓞 →ₐ[𝓞] R₀ v,
      (∀ v i, π v (X i) = x v i) ∧
      (∀ v, Function.Surjective (π v)) ∧
      (∀ v, (t₀ v).comp (π (v + 1)) = π v) ∧
      (∀ v i, π v (X i) ∈ (Ideal.span {(p : R₀ v)}).radical) ∧
      (∀ v G, π v G = MvFormalGroup.adicEval (Ideal.span {(p : R₀ v)}) (fun i => π v (X i)) G) ∧
      (∀ G, (∀ v, π v G = 0) → G = 0) ∧
      (∀ z : ∀ v, R₀ v, (∀ v, t₀ v (z (v + 1)) = z v) → ∃ G, ∀ v, π v G = z v) := by
  classical
  have hk : Function.Surjective (algebraMap 𝓞 (ZMod p)) := ZMod.ringHom_surjective _
  let πbar : ∀ v, MvPolynomial σ (ZMod p) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) (R₀ v) :=
    fun v => MvPolynomial.aeval fun i => (1 : ZMod p) ⊗ₜ[𝓞] x v i
  have hxred : ∀ v i, red 𝓞 p (R₀ v) (x v i) = πbar v (MvPolynomial.X i) := by
    intro v i
    rw [red_apply]
    exact (MvPolynomial.aeval_X (fun i => (1 : ZMod p) ⊗ₜ[𝓞] x v i) i).symm
  have hπc : ∀ v (P : MvPolynomial σ (ZMod p)),
      Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (t₀ v) (πbar (v + 1) P) = πbar v P := by
    intro v P
    rw [← AlgHom.comp_apply]
    congr 1
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply]
    simp only [πbar, MvPolynomial.aeval_X, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hxt v i]
  refine ⟨evalAt 𝓞 p R₀ x hxrad, fun v i => evalAt_X p R₀ x hxrad v i,
    fun v => evalAt_surjective p R₀ x hxrad πbar hxred hk hker hxsurj v,
    fun v => comp_evalAt p R₀ x hxrad t₀ hxt v, fun v i => ?_, fun v G => ?_,
    fun G hG => eq_zero_of_forall_evalAt_eq_zero p R₀ x hxrad πbar hxred hker hxsurj hp0 hxker hG,
    fun z hz => exists_forall_evalAt_eq p R₀ t₀ x hxrad πbar hxred hπc hk hker hxsurj hp0 hxker z hz⟩
  · rw [evalAt_X]
    exact hxrad v i
  · rw [evalAt_apply]
    congr 1
    funext i
    exact (evalAt_X p R₀ x hxrad v i).symm

open MvPowerSeries
open scoped TensorProduct

namespace CoordLaw

section Coeff

variable {R : Type*} [CommRing R] {d : ℕ}

private noncomputable def zfam (d : ℕ) (R : Type*) [CommRing R] :
    Fin d ⊕ Fin d → MvPowerSeries (Fin d) R :=
  Sum.elim (fun j => (X j : MvPowerSeries (Fin d) R)) fun _ => 0

private theorem constantCoeff_zfam (s : Fin d ⊕ Fin d) : (zfam d R s).constantCoeff = 0 := by
  rcases s with l | l
  · exact constantCoeff_X l
  · exact map_zero _

private theorem hasSubst_zfam : HasSubst (zfam d R) :=
  hasSubst_of_constantCoeff_zero constantCoeff_zfam

private theorem prod_pow_comp_inl :
    ((fun (s : Fin d ⊕ Fin d) (e : ℕ) => zfam d R s ^ e) ∘ Sum.inl)
      = fun (l : Fin d) (e : ℕ) => (X l : MvPowerSeries (Fin d) R) ^ e := by
  funext l e
  rfl

private theorem prod_pow_comp_inr :
    ((fun (s : Fin d ⊕ Fin d) (e : ℕ) => zfam d R s ^ e) ∘ Sum.inr)
      = fun (_ : Fin d) (e : ℕ) => (0 : MvPowerSeries (Fin d) R) ^ e := by
  funext l e
  rfl

private theorem coeff_subst_zfam (g : MvPowerSeries (Fin d ⊕ Fin d) R) (m : Fin d →₀ ℕ) :
    coeff m (subst (zfam d R) g) = coeff (m.sumElim 0) g := by
  classical
  rw [coeff_subst hasSubst_zfam, finsum_eq_single _ (m.sumElim (0 : Fin d →₀ ℕ))]
  · rw [Finsupp.prod_sumElim, prod_pow_comp_inl, Finsupp.prod_zero_index, mul_one,
      ← MvPowerSeries.monomial_one_eq, coeff_monomial_same, smul_eq_mul, mul_one]
  · intro n hn
    obtain ⟨a, b, rfl⟩ : ∃ a b : Fin d →₀ ℕ, n = a.sumElim b :=
      ⟨_, _, (Finsupp.comapDomain_sumElim_comapDomain n).symm⟩
    rw [Finsupp.prod_sumElim, prod_pow_comp_inl, prod_pow_comp_inr]
    by_cases hb : b = 0
    · subst hb
      have hab : m ≠ a := fun h => hn (by rw [h])
      rw [Finsupp.prod_zero_index, mul_one, ← MvPowerSeries.monomial_one_eq,
        coeff_monomial_ne hab, smul_zero]
    · obtain ⟨t, ht⟩ : ∃ t, b t ≠ 0 := by
        by_contra h
        push Not at h
        exact hb (Finsupp.ext h)
      have hz : (b.prod fun (_ : Fin d) (e : ℕ) => (0 : MvPowerSeries (Fin d) R) ^ e) = 0 :=
        Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr ht) (zero_pow ht)
      rw [hz, mul_zero, map_zero, smul_zero]

end Coeff

private theorem algHom_ext_X {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    (J : Ideal S) [IsAdicComplete J S] {τ : Type*} [Finite τ]
    {ψ ψ' : MvPowerSeries τ R →ₐ[R] S} (hψ : ∀ s, ψ (X s) ∈ J.radical)
    (h : ∀ s, ψ (X s) = ψ' (X s)) : ψ = ψ' := by
  apply AlgHom.ext
  intro f
  rw [MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical J ψ hψ f,
    MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical J ψ'
      (fun s => h s ▸ hψ s) f]
  congr 1
  funext s
  exact h s

section Unit

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) {A : Type v} [CommRing A] [Bialgebra 𝓞 A]

private theorem map_id_counitAlgHom_comul (a : A) :
    Algebra.TensorProduct.map (AlgHom.id 𝓞 A) (Bialgebra.counitAlgHom 𝓞 A)
      (Coalgebra.comul (R := 𝓞) a) = a ⊗ₜ[𝓞] (1 : 𝓞) := by
  have h : (Algebra.TensorProduct.map (AlgHom.id 𝓞 A) (Bialgebra.counitAlgHom 𝓞 A)).toLinearMap
      = LinearMap.lTensor A (Coalgebra.counit (R := 𝓞) (A := A)) := by
    apply TensorProduct.ext'
    intro a b
    rfl
  have h2 := LinearMap.congr_fun h (Coalgebra.comul (R := 𝓞) a)
  rw [AlgHom.toLinearMap_apply] at h2
  rw [h2, Coalgebra.lTensor_counit_comul]

private theorem pi_subst_zfam_eq [IsAdicComplete (Ideal.span {(p : A)}) A]
    {d : ℕ} (x : Fin d → A) (hxrad : ∀ j, x j ∈ (Ideal.span {(p : A)}).radical)
    (hxε : ∀ j, Coalgebra.counit (R := 𝓞) (x j) = 0)
    (π : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] A) (hπX : ∀ j, π (X j) = x j)
    (π₂ : MvPowerSeries (Fin d ⊕ Fin d) 𝓞 →ₐ[𝓞] A ⊗[𝓞] A)
    (hπ₂X : ∀ s, π₂ (X s) = Sum.elim (fun j => x j ⊗ₜ[𝓞] (1 : A)) (fun j => (1 : A) ⊗ₜ[𝓞] x j) s)
    (F : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞)
    (hFΔ : ∀ i, π₂ (F i) = Coalgebra.comul (R := 𝓞) (x i)) (i : Fin d) :
    π (subst (zfam d 𝓞) (F i)) = x i := by
  have heq : π.comp (substAlgHom (hasSubst_zfam (d := d) (R := 𝓞)))
      = ((Algebra.TensorProduct.rid 𝓞 𝓞 A).toAlgHom.comp
          (Algebra.TensorProduct.map (AlgHom.id 𝓞 A) (Bialgebra.counitAlgHom 𝓞 A))).comp π₂ := by
    apply algHom_ext_X (Ideal.span {(p : A)})
    · rintro (j | j)
      · rw [AlgHom.comp_apply, substAlgHom_apply, subst_X hasSubst_zfam]
        show π (X j) ∈ _
        rw [hπX]
        exact hxrad j
      · rw [AlgHom.comp_apply, substAlgHom_apply, subst_X hasSubst_zfam]
        show π 0 ∈ _
        rw [map_zero]
        exact Ideal.zero_mem _
    · rintro (j | j)
      · rw [AlgHom.comp_apply, substAlgHom_apply, subst_X hasSubst_zfam, AlgHom.comp_apply,
          AlgHom.comp_apply, hπ₂X]
        show π (X j) = _
        rw [hπX]
        simp
      · rw [AlgHom.comp_apply, substAlgHom_apply, subst_X hasSubst_zfam, AlgHom.comp_apply,
          AlgHom.comp_apply, hπ₂X]
        show π 0 = _
        rw [map_zero]
        simp [hxε]
  have h := AlgHom.congr_fun heq (F i)
  rw [AlgHom.comp_apply, substAlgHom_apply, AlgHom.comp_apply, AlgHom.comp_apply, hFΔ,
    map_id_counitAlgHom_comul] at h
  rw [h]
  simp

end Unit

section Pair

variable {𝓞 : Type u} [CommRing 𝓞]

private theorem pairTower (p : ℕ) [Fact p.Prime] (hp0 : (p : 𝓞) = 0)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (R : ℕ → Type v) [∀ v, CommRing (R v)] [∀ v, Algebra 𝓞 (R v)]
    [∀ v, Module.Free 𝓞 (R v)] [∀ v, Module.Finite 𝓞 (R v)]
    (t : ∀ v, R (v + 1) →ₐ[𝓞] R v)
    {σ : Type} [Finite σ] (x : ∀ v, σ → R v) (hxt : ∀ v i, t v (x (v + 1) i) = x v i)
    (hxrad : ∀ v i, x v i ∈ (Ideal.span {(p : R v)}).radical)
    (hxsurj : ∀ v, Function.Surjective
      (MvPolynomial.aeval (fun i => (1 : ZMod p) ⊗ₜ[𝓞] x v i) :
        MvPolynomial σ (ZMod p) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) (R v)))
    (hxker : ∀ N : ℕ, ∃ v, RingHom.ker
      (MvPolynomial.aeval (fun i => (1 : ZMod p) ⊗ₜ[𝓞] x v i) :
        MvPolynomial σ (ZMod p) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) (R v)) ≤
      (Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ (ZMod p)))) ^ N)
    (R' : ℕ → Type v) [∀ v, CommRing (R' v)] [∀ v, Algebra 𝓞 (R' v)]
    [∀ v, Module.Free 𝓞 (R' v)] [∀ v, Module.Finite 𝓞 (R' v)]
    (t' : ∀ v, R' (v + 1) →ₐ[𝓞] R' v)
    {σ' : Type} [Finite σ'] (x' : ∀ v, σ' → R' v) (hxt' : ∀ v i, t' v (x' (v + 1) i) = x' v i)
    (hxrad' : ∀ v i, x' v i ∈ (Ideal.span {(p : R' v)}).radical)
    (hxsurj' : ∀ v, Function.Surjective
      (MvPolynomial.aeval (fun i => (1 : ZMod p) ⊗ₜ[𝓞] x' v i) :
        MvPolynomial σ' (ZMod p) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) (R' v)))
    (hxker' : ∀ N : ℕ, ∃ v, RingHom.ker
      (MvPolynomial.aeval (fun i => (1 : ZMod p) ⊗ₜ[𝓞] x' v i) :
        MvPolynomial σ' (ZMod p) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) (R' v)) ≤
      (Ideal.span (Set.range (MvPolynomial.X : σ' → MvPolynomial σ' (ZMod p)))) ^ N) :
    ((∀ v s, Algebra.TensorProduct.map (t v) (t' v)
        (Sum.elim (fun i => x (v + 1) i ⊗ₜ[𝓞] (1 : R' (v + 1)))
          (fun i => (1 : R (v + 1)) ⊗ₜ[𝓞] x' (v + 1) i) s) =
      Sum.elim (fun i => x v i ⊗ₜ[𝓞] (1 : R' v)) (fun i => (1 : R v) ⊗ₜ[𝓞] x' v i) s) ∧
    (∀ v s, Sum.elim (fun i => x v i ⊗ₜ[𝓞] (1 : R' v)) (fun i => (1 : R v) ⊗ₜ[𝓞] x' v i) s ∈
      (Ideal.span {(p : R v ⊗[𝓞] R' v)}).radical) ∧
    (∀ v, Function.Surjective
      (MvPolynomial.aeval (fun s => (1 : ZMod p) ⊗ₜ[𝓞]
          Sum.elim (fun i => x v i ⊗ₜ[𝓞] (1 : R' v)) (fun i => (1 : R v) ⊗ₜ[𝓞] x' v i) s) :
        MvPolynomial (σ ⊕ σ') (ZMod p) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) (R v ⊗[𝓞] R' v))) ∧
    (∀ N : ℕ, ∃ v, RingHom.ker
      (MvPolynomial.aeval (fun s => (1 : ZMod p) ⊗ₜ[𝓞]
          Sum.elim (fun i => x v i ⊗ₜ[𝓞] (1 : R' v)) (fun i => (1 : R v) ⊗ₜ[𝓞] x' v i) s) :
        MvPolynomial (σ ⊕ σ') (ZMod p) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) (R v ⊗[𝓞] R' v)) ≤
      (Ideal.span (Set.range
        (MvPolynomial.X : σ ⊕ σ' → MvPolynomial (σ ⊕ σ') (ZMod p)))) ^ N)) ∧
    ∃ π : ∀ v, MvPowerSeries (σ ⊕ σ') 𝓞 →ₐ[𝓞] R v ⊗[𝓞] R' v,
      (∀ v s, π v (X s) =
        Sum.elim (fun i => x v i ⊗ₜ[𝓞] (1 : R' v)) (fun i => (1 : R v) ⊗ₜ[𝓞] x' v i) s) ∧
      (∀ v, Function.Surjective (π v)) ∧
      (∀ v, (Algebra.TensorProduct.map (t v) (t' v)).comp (π (v + 1)) = π v) ∧
      (∀ v s, π v (X s) ∈ (Ideal.span {(p : R v ⊗[𝓞] R' v)}).radical) ∧
      (∀ v G, π v G =
        MvFormalGroup.adicEval (Ideal.span {(p : R v ⊗[𝓞] R' v)}) (fun s => π v (X s)) G) ∧
      (∀ G, (∀ v, π v G = 0) → G = 0) ∧
      (∀ z : ∀ v, R v ⊗[𝓞] R' v,
        (∀ v, Algebra.TensorProduct.map (t v) (t' v) (z (v + 1)) = z v) → ∃ G, ∀ v, π v G = z v) := by
  obtain ⟨h1, h2, h3, h4⟩ :=
    Algebra.TensorProduct.specialFibre_coordinates_sumElim_tmul (𝓞 := 𝓞) p R t x hxt hxrad hxsurj
      hxker R' t' x' hxt' hxrad' hxsurj' hxker'
  obtain ⟨π, a1, a2, a3, a4, a5, a6, a7⟩ :=
    CoordUp.Up (𝓞 := 𝓞)
      p hp0 hker (fun v => R v ⊗[𝓞] R' v) (fun v => Algebra.TensorProduct.map (t v) (t' v))
      (fun v => Sum.elim (fun i => x v i ⊗ₜ[𝓞] (1 : R' v)) (fun i => (1 : R v) ⊗ₜ[𝓞] x' v i))
      h1 h2 h3 h4
  exact ⟨⟨h1, h2, h3, h4⟩, π, a1, a2, a3, a4, a5, a6, a7⟩

end Pair

end CoordLaw

namespace CoordLawS4

section Aux

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) {A : Type v} [CommRing A] [Algebra 𝓞 A]

private theorem tmul_one_mem_radical {B : Type*} [CommRing B] [Algebra 𝓞 B] {a : A}
    (ha : a ∈ (Ideal.span {(p : A)}).radical) :
    a ⊗ₜ[𝓞] (1 : B) ∈ (Ideal.span {(p : A ⊗[𝓞] B)}).radical := by
  obtain ⟨n, hn⟩ := ha
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hn
  refine ⟨n, ?_⟩
  rw [Algebra.TensorProduct.tmul_pow, one_pow, ← hc,
    show (c * (p : A)) ⊗ₜ[𝓞] (1 : B) = (c ⊗ₜ[𝓞] (1 : B)) * ((p : A) ⊗ₜ[𝓞] (1 : B)) by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one],
    ← Algebra.TensorProduct.natCast_def]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

private theorem one_tmul_mem_radical {B : Type*} [CommRing B] [Algebra 𝓞 B] {b : B}
    (hb : b ∈ (Ideal.span {(p : B)}).radical) :
    (1 : A) ⊗ₜ[𝓞] b ∈ (Ideal.span {(p : A ⊗[𝓞] B)}).radical := by
  obtain ⟨n, hn⟩ := hb
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hn
  refine ⟨n, ?_⟩
  rw [Algebra.TensorProduct.tmul_pow, one_pow, ← hc,
    show (1 : A) ⊗ₜ[𝓞] (c * (p : B)) = ((1 : A) ⊗ₜ[𝓞] c) * ((1 : A) ⊗ₜ[𝓞] (p : B)) by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one],
    ← Algebra.TensorProduct.natCast_def']
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

private theorem algHom_eq_of_forall_X {S : Type*} [CommRing S] [Algebra 𝓞 S] (J : Ideal S)
    [IsAdicComplete J S] {τ : Type*} [Finite τ] (ψ₁ ψ₂ : MvPowerSeries τ 𝓞 →ₐ[𝓞] S)
    (hX : ∀ s, ψ₁ (X s) = ψ₂ (X s)) (hrad : ∀ s, ψ₂ (X s) ∈ J.radical) (f : MvPowerSeries τ 𝓞) :
    ψ₁ f = ψ₂ f := by
  rw [MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical J ψ₁
      (fun s => (hX s).symm ▸ hrad s) f,
    MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical J ψ₂ hrad f]
  congr 1
  funext s
  exact hX s

end Aux

private theorem pi2_subst_swap_eq
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ)
    {A : Type v} [CommRing A] [Bialgebra 𝓞 A] [Coalgebra.IsCocomm 𝓞 A]
    [IsAdicComplete (Ideal.span {(p : A ⊗[𝓞] A)}) (A ⊗[𝓞] A)]
    {d : ℕ} (x : Fin d → A) (hxrad : ∀ j, x j ∈ (Ideal.span {(p : A)}).radical)
    (π₂ : MvPowerSeries (Fin d ⊕ Fin d) 𝓞 →ₐ[𝓞] A ⊗[𝓞] A)
    (hπ₂X : ∀ s, π₂ (X s) = Sum.elim (fun j => x j ⊗ₜ[𝓞] (1 : A)) (fun j => (1 : A) ⊗ₜ[𝓞] x j) s)
    (F : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞)
    (hFΔ : ∀ i, π₂ (F i) = Coalgebra.comul (R := 𝓞) (x i)) (i : Fin d) :
    π₂ (subst
      (Sum.elim
        (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞))
        fun j => X (Sum.inl j))
      (F i)) = π₂ (F i) := by
  classical
  set sw : Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞 :=
    Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) fun j => X (Sum.inl j)
    with hsw
  have hsw0 : ∀ s, constantCoeff (sw s) = 0 := by
    rintro (j | j) <;> simp [hsw, constantCoeff_X]
  have hswS : HasSubst sw := hasSubst_of_constantCoeff_zero hsw0
  let ψ₁ : MvPowerSeries (Fin d ⊕ Fin d) 𝓞 →ₐ[𝓞] A ⊗[𝓞] A := π₂.comp (substAlgHom hswS)
  let ψ₂ : MvPowerSeries (Fin d ⊕ Fin d) 𝓞 →ₐ[𝓞] A ⊗[𝓞] A :=
    (Algebra.TensorProduct.comm 𝓞 A A).toAlgHom.comp π₂
  have hψ₁ : ∀ G, ψ₁ G = π₂ (subst sw G) := fun G => by
    simp only [ψ₁, AlgHom.comp_apply, substAlgHom_apply]
  have hψ₂ : ∀ G, ψ₂ G = Algebra.TensorProduct.comm 𝓞 A A (π₂ G) := fun G => rfl
  have hX : ∀ s, ψ₁ (X s) = ψ₂ (X s) := by
    rintro (j | j)
    · rw [hψ₁, hψ₂, subst_X hswS, hsw, Sum.elim_inl, hπ₂X, hπ₂X, Sum.elim_inr, Sum.elim_inl,
        Algebra.TensorProduct.comm_tmul]
    · rw [hψ₁, hψ₂, subst_X hswS, hsw, Sum.elim_inr, hπ₂X, hπ₂X, Sum.elim_inl, Sum.elim_inr,
        Algebra.TensorProduct.comm_tmul]
  have hrad : ∀ s, ψ₂ (X s) ∈ (Ideal.span {(p : A ⊗[𝓞] A)}).radical := by
    rintro (j | j)
    · rw [hψ₂, hπ₂X, Sum.elim_inl, Algebra.TensorProduct.comm_tmul]
      exact one_tmul_mem_radical p (hxrad j)
    · rw [hψ₂, hπ₂X, Sum.elim_inr, Algebra.TensorProduct.comm_tmul]
      exact tmul_one_mem_radical p (hxrad j)
  have key := algHom_eq_of_forall_X (Ideal.span {(p : A ⊗[𝓞] A)}) ψ₁ ψ₂ hX hrad (F i)
  rw [hψ₁, hψ₂, hFΔ] at key
  rw [key, hFΔ]
  exact Coalgebra.comm_comul 𝓞 (x i)

section AuxA

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) {A : Type v} [CommRing A] [Bialgebra 𝓞 A]

private theorem map_mem_radical {B C : Type*} [CommRing B] [Algebra 𝓞 B] [CommRing C] [Algebra 𝓞 C]
    (f : B →ₐ[𝓞] C) {b : B} (hb : b ∈ (Ideal.span {(p : B)}).radical) :
    f b ∈ (Ideal.span {(p : C)}).radical := by
  obtain ⟨n, hn⟩ := hb
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hn
  refine ⟨n, ?_⟩
  rw [← map_pow, ← hc, map_mul, map_natCast]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

private theorem assoc_apply_eq (z : (A ⊗[𝓞] A) ⊗[𝓞] A) :
    Algebra.TensorProduct.assoc 𝓞 𝓞 𝓞 A A A z = _root_.TensorProduct.assoc 𝓞 A A A z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul w c =>
    induction w using TensorProduct.induction_on with
    | zero => rw [TensorProduct.zero_tmul, map_zero, map_zero]
    | tmul a b => rw [Algebra.TensorProduct.assoc_tmul, TensorProduct.assoc_tmul]
    | add u u' hu hu' => rw [TensorProduct.add_tmul, map_add, map_add, hu, hu']
  | add a b ha hb => rw [map_add, map_add, ha, hb]

private theorem map_includeLeft_eq_assoc (z : A ⊗[𝓞] A) :
    Algebra.TensorProduct.map (AlgHom.id 𝓞 A) (Algebra.TensorProduct.includeLeft : A →ₐ[𝓞] A ⊗[𝓞] A) z =
      Algebra.TensorProduct.assoc 𝓞 𝓞 𝓞 A A A (z ⊗ₜ[𝓞] (1 : A)) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, TensorProduct.zero_tmul, map_zero]
  | tmul a b =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.assoc_tmul]
  | add a b ha hb => rw [map_add, ha, hb, TensorProduct.add_tmul, map_add]

end AuxA

section Assoc

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) {A : Type v} [CommRing A] [Bialgebra 𝓞 A]
  [IsAdicComplete (Ideal.span {(p : A ⊗[𝓞] (A ⊗[𝓞] A))}) (A ⊗[𝓞] (A ⊗[𝓞] A))]
  {d : ℕ} (x : Fin d → A) (hxrad : ∀ j, x j ∈ (Ideal.span {(p : A)}).radical)
  (π₂ : MvPowerSeries (Fin d ⊕ Fin d) 𝓞 →ₐ[𝓞] A ⊗[𝓞] A)
  (hπ₂X : ∀ s, π₂ (X s) = Sum.elim (fun j => x j ⊗ₜ[𝓞] (1 : A)) (fun j => (1 : A) ⊗ₜ[𝓞] x j) s)
  (π₃ : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞 →ₐ[𝓞] A ⊗[𝓞] (A ⊗[𝓞] A))
  (hπ₃X : ∀ s, π₃ (X s) = Sum.elim (fun j => x j ⊗ₜ[𝓞] (1 : A ⊗[𝓞] A))
    (fun s' => (1 : A) ⊗ₜ[𝓞] Sum.elim (fun j => x j ⊗ₜ[𝓞] (1 : A)) (fun j => (1 : A) ⊗ₜ[𝓞] x j) s') s)
  (F : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞) (hF0 : ∀ i, (F i).constantCoeff = 0)
  (hFΔ : ∀ i, π₂ (F i) = Coalgebra.comul (R := 𝓞) (x i))

private noncomputable abbrev β (𝓞 : Type u) [CommRing 𝓞] (d : ℕ) :
    Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞 :=
  Sum.elim (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞))
    fun l => X (Sum.inr (Sum.inl l))

private noncomputable abbrev γ (𝓞 : Type u) [CommRing 𝓞] (d : ℕ) :
    Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞 :=
  Sum.elim (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞))
    fun l => X (Sum.inr (Sum.inr l))

omit [Bialgebra 𝓞 A] in
private theorem hasSubst_β : HasSubst (β 𝓞 d) :=
  hasSubst_of_constantCoeff_zero (by rintro (l | l) <;> simp [constantCoeff_X])

omit [Bialgebra 𝓞 A] in
private theorem hasSubst_γ : HasSubst (γ 𝓞 d) :=
  hasSubst_of_constantCoeff_zero (by rintro (l | l) <;> simp [constantCoeff_X])

include hF0 in
omit [Bialgebra 𝓞 A] in
private theorem hasSubst_αL : HasSubst (Sum.elim (fun j => subst (β 𝓞 d) (F j))
    fun j => (X (Sum.inr (Sum.inr j)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞)) := by
  refine hasSubst_of_constantCoeff_zero ?_
  rintro (j | j)
  · rw [Sum.elim_inl]
    exact constantCoeff_subst_eq_zero (hasSubst_β (𝓞 := 𝓞) (d := d))
      (by rintro (l | l) <;> simp [constantCoeff_X]) (hF0 j)
  · rw [Sum.elim_inr, constantCoeff_X]

include hF0 in
omit [Bialgebra 𝓞 A] in
private theorem hasSubst_αR : HasSubst (Sum.elim
    (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞))
    fun j => subst (γ 𝓞 d) (F j)) := by
  refine hasSubst_of_constantCoeff_zero ?_
  rintro (j | j)
  · rw [Sum.elim_inl, constantCoeff_X]
  · rw [Sum.elim_inr]
    exact constantCoeff_subst_eq_zero (hasSubst_γ (𝓞 := 𝓞) (d := d))
      (by rintro (l | l) <;> simp [constantCoeff_X]) (hF0 j)

include hxrad hπ₂X hπ₃X in

private theorem pi3_subst_β (G : MvPowerSeries (Fin d ⊕ Fin d) 𝓞) :
    π₃ (subst (β 𝓞 d) G) =
      Algebra.TensorProduct.map (AlgHom.id 𝓞 A)
        (Algebra.TensorProduct.includeLeft : A →ₐ[𝓞] A ⊗[𝓞] A) (π₂ G) := by
  have := algHom_eq_of_forall_X (S := A ⊗[𝓞] (A ⊗[𝓞] A)) (Ideal.span {(p : A ⊗[𝓞] (A ⊗[𝓞] A))})
    (π₃.comp (substAlgHom (hasSubst_β (𝓞 := 𝓞) (d := d))))
    ((Algebra.TensorProduct.map (AlgHom.id 𝓞 A)
      (Algebra.TensorProduct.includeLeft : A →ₐ[𝓞] A ⊗[𝓞] A)).comp π₂)
    (by
      rintro (l | l)
      · rw [AlgHom.comp_apply, substAlgHom_apply, subst_X (hasSubst_β (𝓞 := 𝓞) (d := d)), β, Sum.elim_inl, hπ₃X, Sum.elim_inl,
          AlgHom.comp_apply, hπ₂X, Sum.elim_inl, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
          Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.one_def]
      · rw [AlgHom.comp_apply, substAlgHom_apply, subst_X (hasSubst_β (𝓞 := 𝓞) (d := d)), β, Sum.elim_inr, hπ₃X, Sum.elim_inr,
          Sum.elim_inl, AlgHom.comp_apply, hπ₂X, Sum.elim_inr, Algebra.TensorProduct.map_tmul,
          AlgHom.id_apply, Algebra.TensorProduct.includeLeft_apply])
    (by
      rintro (l | l)
      · rw [AlgHom.comp_apply, hπ₂X, Sum.elim_inl, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
          Algebra.TensorProduct.includeLeft_apply]
        exact tmul_one_mem_radical p (hxrad l)
      · rw [AlgHom.comp_apply, hπ₂X, Sum.elim_inr, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
          Algebra.TensorProduct.includeLeft_apply]
        exact one_tmul_mem_radical p (tmul_one_mem_radical p (hxrad l))) G
  rw [AlgHom.comp_apply, substAlgHom_apply, AlgHom.comp_apply] at this
  exact this

include hxrad hπ₂X hπ₃X in

private theorem pi3_subst_γ (G : MvPowerSeries (Fin d ⊕ Fin d) 𝓞) :
    π₃ (subst (γ 𝓞 d) G) =
      (Algebra.TensorProduct.includeRight : A ⊗[𝓞] A →ₐ[𝓞] A ⊗[𝓞] (A ⊗[𝓞] A)) (π₂ G) := by
  have := algHom_eq_of_forall_X (S := A ⊗[𝓞] (A ⊗[𝓞] A)) (Ideal.span {(p : A ⊗[𝓞] (A ⊗[𝓞] A))})
    (π₃.comp (substAlgHom (hasSubst_γ (𝓞 := 𝓞) (d := d))))
    ((Algebra.TensorProduct.includeRight : A ⊗[𝓞] A →ₐ[𝓞] A ⊗[𝓞] (A ⊗[𝓞] A)).comp π₂)
    (by
      rintro (l | l)
      · rw [AlgHom.comp_apply, substAlgHom_apply, subst_X (hasSubst_γ (𝓞 := 𝓞) (d := d)), γ, Sum.elim_inl, hπ₃X, Sum.elim_inr,
          Sum.elim_inl, AlgHom.comp_apply, hπ₂X, Sum.elim_inl, Algebra.TensorProduct.includeRight_apply]
      · rw [AlgHom.comp_apply, substAlgHom_apply, subst_X (hasSubst_γ (𝓞 := 𝓞) (d := d)), γ, Sum.elim_inr, hπ₃X, Sum.elim_inr,
          Sum.elim_inr, AlgHom.comp_apply, hπ₂X, Sum.elim_inr, Algebra.TensorProduct.includeRight_apply])
    (by
      rintro (l | l)
      · rw [AlgHom.comp_apply, hπ₂X, Sum.elim_inl, Algebra.TensorProduct.includeRight_apply]
        exact one_tmul_mem_radical p (tmul_one_mem_radical p (hxrad l))
      · rw [AlgHom.comp_apply, hπ₂X, Sum.elim_inr, Algebra.TensorProduct.includeRight_apply]
        exact one_tmul_mem_radical p (one_tmul_mem_radical p (hxrad l))) G
  rw [AlgHom.comp_apply, substAlgHom_apply, AlgHom.comp_apply] at this
  exact this

include hxrad hπ₂X hπ₃X hF0 hFΔ in

private theorem pi3_subst_αL (G : MvPowerSeries (Fin d ⊕ Fin d) 𝓞) :
    π₃ (subst (Sum.elim (fun j => subst (β 𝓞 d) (F j))
      fun j => (X (Sum.inr (Sum.inr j)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞)) G) =
      ((Algebra.TensorProduct.assoc 𝓞 𝓞 𝓞 A A A).toAlgHom.comp
        (Algebra.TensorProduct.map (Bialgebra.comulAlgHom 𝓞 A) (AlgHom.id 𝓞 A))) (π₂ G) := by
  have := algHom_eq_of_forall_X (S := A ⊗[𝓞] (A ⊗[𝓞] A)) (Ideal.span {(p : A ⊗[𝓞] (A ⊗[𝓞] A))})
    (π₃.comp (substAlgHom (hasSubst_αL (𝓞 := 𝓞) F hF0)))
    (((Algebra.TensorProduct.assoc 𝓞 𝓞 𝓞 A A A).toAlgHom.comp
        (Algebra.TensorProduct.map (Bialgebra.comulAlgHom 𝓞 A) (AlgHom.id 𝓞 A))).comp π₂)
    (by
      rintro (j | j)
      · rw [AlgHom.comp_apply, substAlgHom_apply, subst_X (hasSubst_αL (𝓞 := 𝓞) F hF0), Sum.elim_inl, pi3_subst_β p x hxrad π₂ hπ₂X π₃ hπ₃X,
          hFΔ, map_includeLeft_eq_assoc, AlgHom.comp_apply, hπ₂X, Sum.elim_inl, AlgHom.comp_apply,
          Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Bialgebra.comulAlgHom_apply]
        rfl
      · rw [AlgHom.comp_apply, substAlgHom_apply, subst_X (hasSubst_αL (𝓞 := 𝓞) F hF0), Sum.elim_inr, hπ₃X, Sum.elim_inr, Sum.elim_inr,
          AlgHom.comp_apply, hπ₂X, Sum.elim_inr, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
          AlgHom.id_apply, Bialgebra.comulAlgHom_apply, Bialgebra.comul_one]
        change _ = Algebra.TensorProduct.assoc 𝓞 𝓞 𝓞 A A A (((1 : A) ⊗ₜ[𝓞] (1 : A)) ⊗ₜ[𝓞] x j)
        rw [Algebra.TensorProduct.assoc_tmul])
    (by
      rintro (j | j)
      · rw [AlgHom.comp_apply, hπ₂X, Sum.elim_inl]
        exact map_mem_radical p _ (tmul_one_mem_radical p (hxrad j))
      · rw [AlgHom.comp_apply, hπ₂X, Sum.elim_inr]
        exact map_mem_radical p _ (one_tmul_mem_radical p (hxrad j))) G
  rw [AlgHom.comp_apply, substAlgHom_apply, AlgHom.comp_apply] at this
  exact this

include hxrad hπ₂X hπ₃X hF0 hFΔ in

private theorem pi3_subst_αR (G : MvPowerSeries (Fin d ⊕ Fin d) 𝓞) :
    π₃ (subst (Sum.elim (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞))
      fun j => subst (γ 𝓞 d) (F j)) G) =
      (Algebra.TensorProduct.map (AlgHom.id 𝓞 A) (Bialgebra.comulAlgHom 𝓞 A)) (π₂ G) := by
  have := algHom_eq_of_forall_X (S := A ⊗[𝓞] (A ⊗[𝓞] A)) (Ideal.span {(p : A ⊗[𝓞] (A ⊗[𝓞] A))})
    (π₃.comp (substAlgHom (hasSubst_αR (𝓞 := 𝓞) F hF0)))
    ((Algebra.TensorProduct.map (AlgHom.id 𝓞 A) (Bialgebra.comulAlgHom 𝓞 A)).comp π₂)
    (by
      rintro (j | j)
      · rw [AlgHom.comp_apply, substAlgHom_apply, subst_X (hasSubst_αR (𝓞 := 𝓞) F hF0), Sum.elim_inl, hπ₃X, Sum.elim_inl,
          AlgHom.comp_apply, hπ₂X, Sum.elim_inl, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
          Bialgebra.comulAlgHom_apply, Bialgebra.comul_one, Algebra.TensorProduct.one_def]
      · rw [AlgHom.comp_apply, substAlgHom_apply, subst_X (hasSubst_αR (𝓞 := 𝓞) F hF0), Sum.elim_inr, pi3_subst_γ p x hxrad π₂ hπ₂X π₃ hπ₃X,
          hFΔ, AlgHom.comp_apply, hπ₂X, Sum.elim_inr, Algebra.TensorProduct.includeRight_apply,
          Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Bialgebra.comulAlgHom_apply])
    (by
      rintro (j | j)
      · rw [AlgHom.comp_apply, hπ₂X, Sum.elim_inl]
        exact map_mem_radical p _ (tmul_one_mem_radical p (hxrad j))
      · rw [AlgHom.comp_apply, hπ₂X, Sum.elim_inr]
        exact map_mem_radical p _ (one_tmul_mem_radical p (hxrad j))) G
  rw [AlgHom.comp_apply, substAlgHom_apply, AlgHom.comp_apply] at this
  exact this

end Assoc

private theorem pi3_subst_assoc_eq
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ)
    {A : Type v} [CommRing A] [Bialgebra 𝓞 A]
    [IsAdicComplete (Ideal.span {(p : A ⊗[𝓞] A)}) (A ⊗[𝓞] A)]
    [IsAdicComplete (Ideal.span {(p : A ⊗[𝓞] (A ⊗[𝓞] A))}) (A ⊗[𝓞] (A ⊗[𝓞] A))]
    {d : ℕ} (x : Fin d → A) (hxrad : ∀ j, x j ∈ (Ideal.span {(p : A)}).radical)
    (π₂ : MvPowerSeries (Fin d ⊕ Fin d) 𝓞 →ₐ[𝓞] A ⊗[𝓞] A)
    (hπ₂X : ∀ s, π₂ (X s) = Sum.elim (fun j => x j ⊗ₜ[𝓞] (1 : A)) (fun j => (1 : A) ⊗ₜ[𝓞] x j) s)
    (π₃ : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞 →ₐ[𝓞] A ⊗[𝓞] (A ⊗[𝓞] A))
    (hπ₃X : ∀ s, π₃ (X s) = Sum.elim (fun j => x j ⊗ₜ[𝓞] (1 : A ⊗[𝓞] A))
      (fun s' => (1 : A) ⊗ₜ[𝓞] Sum.elim (fun j => x j ⊗ₜ[𝓞] (1 : A)) (fun j => (1 : A) ⊗ₜ[𝓞] x j) s') s)
    (F : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞) (hF0 : ∀ i, (F i).constantCoeff = 0)
    (hFΔ : ∀ i, π₂ (F i) = Coalgebra.comul (R := 𝓞) (x i)) (i : Fin d) :
    π₃ (subst
      (Sum.elim
        (fun j => subst
          (Sum.elim
            (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞))
            fun l => X (Sum.inr (Sum.inl l)))
          (F j))
        fun j => X (Sum.inr (Sum.inr j)))
      (F i)) =
    π₃ (subst
      (Sum.elim
        (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞))
        fun j => subst
          (Sum.elim
            (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞))
            fun l => X (Sum.inr (Sum.inr l)))
          (F j))
      (F i)) := by
  rw [pi3_subst_αL p x hxrad π₂ hπ₂X π₃ hπ₃X F hF0 hFΔ, pi3_subst_αR p x hxrad π₂ hπ₂X π₃ hπ₃X F hF0 hFΔ, hFΔ]

  have hL : ((Algebra.TensorProduct.assoc 𝓞 𝓞 𝓞 A A A).toAlgHom.comp
      (Algebra.TensorProduct.map (Bialgebra.comulAlgHom 𝓞 A) (AlgHom.id 𝓞 A)))
        (Coalgebra.comul (R := 𝓞) (x i)) =
      _root_.TensorProduct.assoc 𝓞 A A A
        ((Coalgebra.comul (R := 𝓞) (A := A)).rTensor A (Coalgebra.comul (R := 𝓞) (x i))) := by
    generalize Coalgebra.comul (R := 𝓞) (x i) = z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul a b =>
      rw [LinearMap.rTensor_tmul, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        Bialgebra.comulAlgHom_apply, ← assoc_apply_eq]
      rfl
    | add a b ha hb => rw [map_add, ha, hb, map_add, map_add]
  have hR : (Algebra.TensorProduct.map (AlgHom.id 𝓞 A) (Bialgebra.comulAlgHom 𝓞 A))
        (Coalgebra.comul (R := 𝓞) (x i)) =
      (Coalgebra.comul (R := 𝓞) (A := A)).lTensor A (Coalgebra.comul (R := 𝓞) (x i)) := by
    generalize Coalgebra.comul (R := 𝓞) (x i) = z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a b =>
      rw [LinearMap.lTensor_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Bialgebra.comulAlgHom_apply]
    | add a b ha hb => rw [map_add, ha, hb, map_add]
  rw [hL, hR]
  exact Coalgebra.coassoc_apply (x i)

end CoordLawS4

open CoordLaw in
theorem CoordLaw.law
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp0 : (p : 𝓞) = 0)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (R₀ : ℕ → Type v) [∀ v, CommRing (R₀ v)] [∀ v, HopfAlgebra 𝓞 (R₀ v)]
    [∀ v, Coalgebra.IsCocomm 𝓞 (R₀ v)] [∀ v, Module.Free 𝓞 (R₀ v)] [∀ v, Module.Finite 𝓞 (R₀ v)]
    (t₀ : ∀ v, R₀ (v + 1) →ₐc[𝓞] R₀ v)
    (d : ℕ) (x : ∀ v, Fin d → R₀ v) (hxt : ∀ v i, t₀ v (x (v + 1) i) = x v i)
    (hxε : ∀ v i, Coalgebra.counit (R := 𝓞) (x v i) = 0)
    (hxrad : ∀ v i, x v i ∈ (Ideal.span {(p : R₀ v)}).radical)
    (hxsurj : ∀ v, Function.Surjective
      (MvPolynomial.aeval (fun i => (1 : ZMod p) ⊗ₜ[𝓞] x v i) :
        MvPolynomial (Fin d) (ZMod p) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) (R₀ v)))
    (hxker : ∀ N : ℕ, ∃ v, RingHom.ker
      (MvPolynomial.aeval (fun i => (1 : ZMod p) ⊗ₜ[𝓞] x v i) :
        MvPolynomial (Fin d) (ZMod p) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) (R₀ v)) ≤
      (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) (ZMod p)))) ^ N) :
    ∃ (F : MvFormalGroup d 𝓞) (_ : F.IsComm) (π : ∀ v, MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] R₀ v),
      (∀ v i, π v (X i) = x v i) ∧
      (∀ v, Function.Surjective (π v)) ∧
      (∀ v, (t₀ v : R₀ (v + 1) →ₐ[𝓞] R₀ v).comp (π (v + 1)) = π v) ∧
      (∀ v i, π v (X i) ∈ (Ideal.span {(p : R₀ v)}).radical) ∧
      (∀ v G, π v G = MvFormalGroup.adicEval (Ideal.span {(p : R₀ v)}) (fun i => π v (X i)) G) ∧
      (∀ G, (∀ v, π v G = 0) → G = 0) ∧
      (∀ z : ∀ v, R₀ v, (∀ v, t₀ v (z (v + 1)) = z v) → ∃ G, ∀ v, π v G = z v) ∧
      (∀ v i, Coalgebra.counit (R := 𝓞) (π v (X i)) = 0) ∧
      (∀ v i, Coalgebra.comul (R := 𝓞) (π v (X i)) =
        MvFormalGroup.adicEval (Ideal.span {(p : R₀ v ⊗[𝓞] R₀ v)})
          (Sum.elim (fun j => π v (X j) ⊗ₜ[𝓞] (1 : R₀ v)) (fun j => (1 : R₀ v) ⊗ₜ[𝓞] π v (X j)))
          (F.toPowerSeries i)) := by
  classical

  haveI hc1 : ∀ v, IsAdicComplete (Ideal.span {(p : R₀ v)}) (R₀ v) := fun v =>
    IsAdicComplete.of_module_finite_free_span_natCast (𝓞 := 𝓞) p (R₀ v)
  haveI hc2 : ∀ v, IsAdicComplete (Ideal.span {(p : R₀ v ⊗[𝓞] R₀ v)}) (R₀ v ⊗[𝓞] R₀ v) :=
    fun v => IsAdicComplete.of_module_finite_free_span_natCast (𝓞 := 𝓞) p (R₀ v ⊗[𝓞] R₀ v)
  haveI hc3 : ∀ v, IsAdicComplete (Ideal.span {(p : R₀ v ⊗[𝓞] (R₀ v ⊗[𝓞] R₀ v))})
      (R₀ v ⊗[𝓞] (R₀ v ⊗[𝓞] R₀ v)) :=
    fun v => IsAdicComplete.of_module_finite_free_span_natCast (𝓞 := 𝓞) p (R₀ v ⊗[𝓞] (R₀ v ⊗[𝓞] R₀ v))

  have hxt₁ : ∀ v i, (t₀ v : R₀ (v + 1) →ₐ[𝓞] R₀ v) (x (v + 1) i) = x v i := fun v i => by
    rw [BialgHom.coe_toAlgHom]
    exact hxt v i

  obtain ⟨π, hπX, hπsurj, hπcomp, hπrad, hπeval, hπinj, hπjs⟩ :=
    CoordUp.Up (𝓞 := 𝓞) p hp0 hker R₀
      (fun v => (t₀ v : R₀ (v + 1) →ₐ[𝓞] R₀ v)) x hxt₁ hxrad hxsurj hxker

  obtain ⟨⟨h2t, h2rad, h2surj, h2ker⟩, π₂, hπ₂X, -, -, -, hπ₂eval, hπ₂inj, hπ₂js⟩ :=
    pairTower (𝓞 := 𝓞) p hp0 hker R₀ (fun v => (t₀ v : R₀ (v + 1) →ₐ[𝓞] R₀ v)) x hxt₁ hxrad
      hxsurj hxker R₀ (fun v => (t₀ v : R₀ (v + 1) →ₐ[𝓞] R₀ v)) x hxt₁ hxrad hxsurj hxker
  obtain ⟨-, π₃, hπ₃X, -, -, -, -, hπ₃inj, -⟩ :=
    pairTower (𝓞 := 𝓞) p hp0 hker R₀ (fun v => (t₀ v : R₀ (v + 1) →ₐ[𝓞] R₀ v)) x hxt₁ hxrad
      hxsurj hxker (fun v => R₀ v ⊗[𝓞] R₀ v)
      (fun v => Algebra.TensorProduct.map (t₀ v : R₀ (v + 1) →ₐ[𝓞] R₀ v)
        (t₀ v : R₀ (v + 1) →ₐ[𝓞] R₀ v))
      (fun v => Sum.elim (fun i => x v i ⊗ₜ[𝓞] (1 : R₀ v)) (fun i => (1 : R₀ v) ⊗ₜ[𝓞] x v i))
      h2t h2rad h2surj h2ker

  have hz : ∀ i v, Algebra.TensorProduct.map (t₀ v : R₀ (v + 1) →ₐ[𝓞] R₀ v)
      (t₀ v : R₀ (v + 1) →ₐ[𝓞] R₀ v) (Coalgebra.comul (R := 𝓞) (x (v + 1) i))
      = Coalgebra.comul (R := 𝓞) (x v i) := by
    intro i v
    have h := AlgHom.congr_fun (BialgHom.map_comp_comulAlgHom (t₀ v)) (x (v + 1) i)
    rw [AlgHom.comp_apply, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply,
      Bialgebra.comulAlgHom_apply, BialgHom.coe_toAlgHom, hxt] at h
    exact h
  choose F hF using fun i => hπ₂js (fun v => Coalgebra.comul (R := 𝓞) (x v i)) (hz i)

  have hunit : ∀ i, subst (zfam d 𝓞) (F i) = X i := fun i => by
    refine sub_eq_zero.mp (hπinj _ fun v => ?_)
    rw [map_sub, hπX, pi_subst_zfam_eq p (x v) (hxrad v) (hxε v) (π v) (hπX v) (π₂ v) (hπ₂X v)
      F (fun i => hF i v) i, sub_self]
  have hF0 : ∀ i, (F i).constantCoeff = 0 := fun i => by
    rw [← coeff_zero_eq_constantCoeff_apply, ← Finsupp.sumElim_zero_zero, ← coeff_subst_zfam,
      hunit, coeff_zero_X]
  have hinl : ∀ i j, (F i).coeff (Finsupp.single (Sum.inl j) 1) = if i = j then 1 else 0 := by
    intro i j
    rw [← Finsupp.sumElim_single_zero, ← coeff_subst_zfam, hunit, coeff_index_single_X]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]

  have hcomm : ∀ i, subst (Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞))
      fun j => X (Sum.inl j)) (F i) = F i := fun i => by
    refine sub_eq_zero.mp (hπ₂inj _ fun v => ?_)
    rw [map_sub, CoordLawS4.pi2_subst_swap_eq p (x v) (hxrad v) (π₂ v) (hπ₂X v) F (fun i => hF i v) i,
      sub_self]
  have hassoc : ∀ i,
      subst
        (Sum.elim
          (fun j => subst
            (Sum.elim
              (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞))
              fun l => X (Sum.inr (Sum.inl l)))
            (F j))
          fun j => X (Sum.inr (Sum.inr j)))
        (F i)
        =
      subst
        (Sum.elim
          (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞))
          fun j => subst
            (Sum.elim
              (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) 𝓞))
              fun l => X (Sum.inr (Sum.inr l)))
            (F j))
        (F i) := fun i => by
    refine sub_eq_zero.mp (hπ₃inj _ fun v => ?_)
    rw [map_sub, CoordLawS4.pi3_subst_assoc_eq p (x v) (hxrad v) (π₂ v) (hπ₂X v) (π₃ v) (hπ₃X v) F hF0
      (fun i => hF i v) i, sub_self]

  have hinr : ∀ i j, (F i).coeff (Finsupp.single (Sum.inr j) 1) = if i = j then 1 else 0 := by
    intro i j
    have hc0 : ∀ s : Fin d ⊕ Fin d, ((Sum.elim
        (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞))
        fun j => X (Sum.inl j)) s).constantCoeff = 0 := by
      rintro (s | s) <;> exact constantCoeff_X _
    rw [← hcomm i, MvFormalGroup.coeff_single_subst hc0 (F i) (Sum.inr j), Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, coeff_index_single_X, Sum.inr.injEq, reduceCtorEq,
      if_false, mul_zero, Finset.sum_const_zero, add_zero, mul_ite, mul_one,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact hinl i j

  let Flaw : MvFormalGroup d 𝓞 :=
    { toPowerSeries := F
      constantCoeff_eq_zero := hF0
      coeff_single_inl := hinl
      coeff_single_inr := hinr
      assoc := hassoc }
  refine ⟨Flaw, ⟨hcomm⟩, π, hπX, hπsurj, hπcomp, hπrad, hπeval, hπinj, hπjs, fun v i => ?_,
    fun v i => ?_⟩
  · rw [hπX]
    exact hxε v i
  · simp only [hπX]
    rw [← hF i v, hπ₂eval v (F i)]
    congr 1
    funext s
    rcases s with j | j
    · rw [hπ₂X]
    · rw [hπ₂X]

open MvPowerSeries
open scoped TensorProduct

namespace CoordTransfer

section PS

variable (p : ℕ) [Fact p.Prime] {d : ℕ}

private theorem coeff_eq_zero_of_mem_pow {N : ℕ} {G : MvPowerSeries (Fin d) (ZMod p)}
    (hG : G ∈ (Ideal.span (Set.range (MvPowerSeries.X : Fin d → MvPowerSeries (Fin d) (ZMod p)))) ^ N)
    {m : Fin d →₀ ℕ} (hm : m.degree < N) : MvPowerSeries.coeff m G = 0 := by
  classical

  let K : ℕ → Ideal (MvPowerSeries (Fin d) (ZMod p)) := fun n =>
    { carrier := {G | ∀ m : Fin d →₀ ℕ, m.degree < n → MvPowerSeries.coeff m G = 0}
      add_mem' := fun {a b} ha hb m hm => by rw [map_add, ha m hm, hb m hm, add_zero]
      zero_mem' := fun m _ => by rw [map_zero]
      smul_mem' := fun c {a} ha m hm => by
        rw [smul_eq_mul, MvPowerSeries.coeff_mul]
        refine Finset.sum_eq_zero fun q hq => ?_
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
        have : q.2.degree < n := lt_of_le_of_lt (by rw [← hq, map_add]; exact Nat.le_add_left _ _) hm
        rw [ha q.2 this, mul_zero] }
  have hK : ∀ n, (Ideal.span (Set.range (MvPowerSeries.X : Fin d → MvPowerSeries (Fin d) (ZMod p)))) ^ n ≤ K n := by
    intro n
    induction n with
    | zero => intro G _ m hm; exact absurd hm (Nat.not_lt_zero _)
    | succ n ih =>
      rw [pow_succ]
      refine (Ideal.mul_mono_left ih).trans ?_
      rw [Ideal.mul_le]
      intro a ha b hb
      refine Submodule.span_induction (p := fun b _ => a * b ∈ K (n + 1)) ?_ ?_ ?_ ?_ hb
      · rintro _ ⟨i, rfl⟩ m hm
        rw [MvPowerSeries.coeff_mul]
        refine Finset.sum_eq_zero fun q hq => ?_
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
        rw [MvPowerSeries.coeff_X]
        split_ifs with h
        · have : q.1.degree < n := by
            have h1 : m.degree = q.1.degree + q.2.degree := by rw [← hq, map_add]
            rw [h, Finsupp.degree_single] at h1
            omega
          rw [ha q.1 this, zero_mul]
        · rw [mul_zero]
      · intro m _; rw [mul_zero, map_zero]
      · intro u w _ _ hu hw m hm; rw [mul_add, map_add, hu m hm, hw m hm, add_zero]
      · intro c u _ hu m hm
        rw [smul_eq_mul, mul_left_comm]
        exact (K (n + 1)).smul_mem c hu m hm
  exact hK N hG m hm

variable {A : Type v} [CommRing A] [Algebra (ZMod p) A]

private theorem exists_coe_sub_mem_pow (G : MvPowerSeries (Fin d) (ZMod p)) (M : ℕ) :
    ∃ P : MvPolynomial (Fin d) (ZMod p), G - P ∈
      (Ideal.span (Set.range (MvPowerSeries.X : Fin d → MvPowerSeries (Fin d) (ZMod p)))) ^ M := by
  classical
  let S : Finset (Fin d →₀ ℕ) := (Finsupp.finite_of_degree_lt (σ := Fin d) M).toFinset
  refine ⟨∑ m ∈ S, MvPolynomial.monomial m (MvPowerSeries.coeff m G), ?_⟩
  refine MvPowerSeries.mem_pow_span_X_of_coeff_eq_zero M _ fun m hm => ?_
  have hmS : m ∈ S := (Set.Finite.mem_toFinset _).2 hm
  rw [map_sub, MvPolynomial.coeff_coe, MvPolynomial.coeff_sum, Finset.sum_eq_single m, MvPolynomial.coeff_monomial,
    if_pos rfl, sub_self]
  · intro m' _ hne; rw [MvPolynomial.coeff_monomial, if_neg hne]
  · intro h; exact absurd hmS h

private theorem map_pow_X_eq_zero (φ : MvPowerSeries (Fin d) (ZMod p) →ₐ[ZMod p] A) (I : Ideal A) {M : ℕ}
    (hI : I ^ M = ⊥) (hφ : ∀ i, φ (MvPowerSeries.X i) ∈ I) {G : MvPowerSeries (Fin d) (ZMod p)}
    (hG : G ∈ (Ideal.span (Set.range (MvPowerSeries.X : Fin d → MvPowerSeries (Fin d) (ZMod p)))) ^ M) : φ G = 0 := by
  have h := Ideal.mem_map_of_mem (φ : MvPowerSeries (Fin d) (ZMod p) →+* A) hG
  rw [Ideal.map_pow, Ideal.map_span] at h
  have hle : Ideal.span ((φ : MvPowerSeries (Fin d) (ZMod p) →+* A) ''
      Set.range (MvPowerSeries.X : Fin d → MvPowerSeries (Fin d) (ZMod p))) ≤ I := by
    rw [Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact hφ i
  have := Ideal.pow_right_mono hle M h
  rw [hI] at this
  exact (Submodule.mem_bot _).1 this

end PS

section Main

private theorem apply_coe_eq_aeval {p d : ℕ} {A : Type v} [CommRing A] [Algebra (ZMod p) A]
    (φ : MvPowerSeries (Fin d) (ZMod p) →ₐ[ZMod p] A) (P : MvPolynomial (Fin d) (ZMod p)) :
    φ (P : MvPowerSeries (Fin d) (ZMod p)) = MvPolynomial.aeval (fun i => φ (X i)) P := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    have hC : ((MvPolynomial.C a : MvPolynomial (Fin d) (ZMod p)) : MvPowerSeries (Fin d) (ZMod p)) =
        algebraMap (ZMod p) (MvPowerSeries (Fin d) (ZMod p)) a := by
      rw [MvPolynomial.coe_C, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self_apply]
    rw [hC, AlgHom.commutes, MvPolynomial.aeval_C]
  | add f g hf hg => rw [MvPolynomial.coe_add, map_add, map_add, hf, hg]
  | mul_X f i hf => rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, map_mul, map_mul, hf, MvPolynomial.aeval_X]

theorem specialFibre_coordinates_of_tower
    (p : ℕ) [Fact p.Prime]
    (G : ℕ → Type v) [∀ v, CommRing (G v)] [∀ v, Algebra (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)]
    (s : ∀ v, G (v + 1) →ₐ[ZMod p] G v)
    {d : ℕ} (π₀ : ∀ v, MvPowerSeries (Fin d) (ZMod p) →ₐ[ZMod p] G v)
    (hπ₀comp : ∀ v, (s v).comp (π₀ (v + 1)) = π₀ v)
    (hπ₀nil : ∀ v i, IsNilpotent (π₀ v (X i)))
    (hπ₀surj : ∀ v, Function.Surjective (π₀ v))
    (hπ₀ker : ∀ N : ℕ, ∃ v, RingHom.ker (π₀ v) ≤
      (Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) (ZMod p)))) ^ N) :
    (∀ v i, s v (π₀ (v + 1) (X i)) = π₀ v (X i)) ∧
    (∀ v i, π₀ v (X i) ∈ (Ideal.span {(p : G v)}).radical) ∧
    (∀ v, Function.Surjective
      (MvPolynomial.aeval (fun i => (1 : ZMod p) ⊗ₜ[ZMod p] π₀ v (X i)) :
        MvPolynomial (Fin d) (ZMod p) →ₐ[ZMod p] TensorProduct (ZMod p) (ZMod p) (G v))) ∧
    (∀ N : ℕ, ∃ v, RingHom.ker
      (MvPolynomial.aeval (fun i => (1 : ZMod p) ⊗ₜ[ZMod p] π₀ v (X i)) :
        MvPolynomial (Fin d) (ZMod p) →ₐ[ZMod p] TensorProduct (ZMod p) (ZMod p) (G v)) ≤
      (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) (ZMod p)))) ^ N) := by
  classical

  have hIM : ∀ v, ∃ M : ℕ, (Ideal.span (Set.range fun i => π₀ v (X i))) ^ M = ⊥ := fun v => by
    have hfg : (Ideal.span (Set.range fun i => π₀ v (X i))).FG := Submodule.fg_span (Set.finite_range _)
    have hle : Ideal.span (Set.range fun i => π₀ v (X i)) ≤ nilradical (G v) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hπ₀nil v i
    obtain ⟨M, hM⟩ := (Ideal.FG.isNilpotent_iff_le_nilradical hfg).2 hle
    exact ⟨M, hM⟩

  have hsurjx : ∀ v, Function.Surjective
      (MvPolynomial.aeval (fun i => π₀ v (X i)) : MvPolynomial (Fin d) (ZMod p) →ₐ[ZMod p] G v) := by
    intro v g
    obtain ⟨F, rfl⟩ := hπ₀surj v g
    obtain ⟨M, hM⟩ := hIM v
    obtain ⟨P, hP⟩ := exists_coe_sub_mem_pow p F M
    refine ⟨P, ?_⟩
    have h0 : π₀ v (F - P) = 0 :=
      map_pow_X_eq_zero p (π₀ v) _ hM (fun i => Ideal.subset_span ⟨i, rfl⟩) hP
    rw [map_sub, sub_eq_zero] at h0
    rw [← apply_coe_eq_aeval, ← h0]

  have hfac : ∀ v, (MvPolynomial.aeval (fun i => (1 : ZMod p) ⊗ₜ[ZMod p] π₀ v (X i)) :
      MvPolynomial (Fin d) (ZMod p) →ₐ[ZMod p] TensorProduct (ZMod p) (ZMod p) (G v)) =
      (Algebra.TensorProduct.includeRight : G v →ₐ[ZMod p] ZMod p ⊗[ZMod p] G v).comp
        (MvPolynomial.aeval fun i => π₀ v (X i)) := fun v =>
    MvPolynomial.algHom_ext fun i => by
      rw [MvPolynomial.aeval_X, AlgHom.comp_apply, MvPolynomial.aeval_X, Algebra.TensorProduct.includeRight_apply]
  refine ⟨fun v i => AlgHom.congr_fun (hπ₀comp v) (X i), fun v i => ?_, fun v => ?_, fun N => ?_⟩
  · obtain ⟨n, hn⟩ := hπ₀nil v i
    exact ⟨n, by rw [hn]; exact Ideal.zero_mem _⟩
  · rw [hfac v, AlgHom.coe_comp]
    refine Function.Surjective.comp (fun z => ?_) (hsurjx v)
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul c g =>
      refine ⟨c • g, ?_⟩
      rw [Algebra.TensorProduct.includeRight_apply, TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul,
        mul_one]
    | add x y hx hy =>
      obtain ⟨r, rfl⟩ := hx
      obtain ⟨t, rfl⟩ := hy
      exact ⟨r + t, map_add _ _ _⟩
  · obtain ⟨v, hv⟩ := hπ₀ker N
    refine ⟨v, fun P hP => ?_⟩
    rw [RingHom.mem_ker, hfac v, AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply] at hP
    have h1 : MvPolynomial.aeval (fun i => π₀ v (X i)) P = 0 := by
      have h := congrArg (Algebra.TensorProduct.lid (ZMod p) (G v)) hP
      rwa [Algebra.TensorProduct.lid_tmul, one_smul, map_zero] at h
    have h2 : (P : MvPowerSeries (Fin d) (ZMod p)) ∈ RingHom.ker (π₀ v) := by
      rw [RingHom.mem_ker, apply_coe_eq_aeval, h1]
    have h3 := hv h2
    rw [MvPolynomial.mem_pow_idealOfVars_iff']
    intro m hm
    rw [← MvPolynomial.coeff_coe]
    exact coeff_eq_zero_of_mem_pow p h3 hm

end Main

end CoordTransfer

open scoped TensorProduct
open MvPowerSeries

namespace CoordKerFin

namespace TorsionLevelLemmas

section Level

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]
variable (R : Type v) [CommRing R] [HopfAlgebra 𝓞 R]
variable [IsAdicComplete (Ideal.span {(p : R)}) R] [IsAdicComplete (Ideal.span {(p : R ⊗[𝓞] R)}) (R ⊗[𝓞] R)]
variable {d : ℕ} (π : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] R)
variable (hπX : ∀ i, π (X i) ∈ (Ideal.span {(p : R)}).radical)
variable (F : MvFormalGroup d 𝓞)
variable (hπΔ : ∀ i, Coalgebra.comul (R := 𝓞) (π (X i)) =
  MvFormalGroup.adicEval (Ideal.span {(p : R ⊗[𝓞] R)})
    (Sum.elim (fun j => π (X j) ⊗ₜ[𝓞] (1 : R)) (fun j => (1 : R) ⊗ₜ[𝓞] π (X j))) (F.toPowerSeries i))

omit [Fact p.Prime] [IsAdicComplete (Ideal.span {(p : R)}) R]
  [IsAdicComplete (Ideal.span {(p : R ⊗[𝓞] R)}) (R ⊗[𝓞] R)] in

private theorem map_mem_radical {B C : Type*} [CommRing B] [Algebra 𝓞 B] [CommRing C] [Algebra 𝓞 C]
    (f : B →ₐ[𝓞] C) {b : B} (hb : b ∈ (Ideal.span {(p : B)}).radical) :
    f b ∈ (Ideal.span {(p : C)}).radical := by
  obtain ⟨n, hn⟩ := hb
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hn
  refine ⟨n, ?_⟩
  rw [← map_pow, ← hc, map_mul, map_natCast]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

private theorem constantCoeff_nthSeries (F : MvFormalGroup d 𝓞) : ∀ (n : ℕ) (j : Fin d),
    MvPowerSeries.constantCoeff (F.nthSeries n j) = 0
  | 0, j => by rw [MvFormalGroup.nthSeries_zero, map_zero]
  | n + 1, j => by
    rw [MvFormalGroup.nthSeries_succ]
    refine constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero ?_) ?_ (F.constantCoeff_eq_zero j)
    · rintro (l | l)
      · exact constantCoeff_nthSeries F n l
      · exact constantCoeff_X l
    · rintro (l | l)
      · exact constantCoeff_nthSeries F n l
      · exact constantCoeff_X l

private theorem hasSubst_nthSeries (F : MvFormalGroup d 𝓞) (n : ℕ) :
    HasSubst (Sum.elim (F.nthSeries n) fun j => (X j : MvPowerSeries (Fin d) 𝓞)) :=
  hasSubst_of_constantCoeff_zero (by
    rintro (l | l)
    · exact constantCoeff_nthSeries F n l
    · exact constantCoeff_X l)

include hπX in
omit [Fact p.Prime] [IsAdicComplete (Ideal.span {(p : R ⊗[𝓞] R)}) (R ⊗[𝓞] R)] in

private theorem apply_eq_adicEval (G : MvPowerSeries (Fin d) 𝓞) :
    π G = MvFormalGroup.adicEval (Ideal.span {(p : R)}) (fun j => π (X j)) G :=
  MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical _ π hπX G

private theorem nsmulAlgHom_succ_apply (n : ℕ) (a : R) :
    PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 R (n + 1) a =
      ((Algebra.TensorProduct.lmul' 𝓞 (S := R)).comp
        (Algebra.TensorProduct.map (PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 R n) (AlgHom.id 𝓞 R)))
        (Coalgebra.comul (R := 𝓞) a) := by
  have h1 : PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 R (n + 1) a =
      LinearMap.mul' 𝓞 R (TensorProduct.map (PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 R n).toLinearMap
        LinearMap.id (Coalgebra.comul (R := 𝓞) a)) := by
    have h := PDivisibleGroup.Hopf.toLinearMap_nsmulAlgHom 𝓞 R (n + 1)
    rw [pow_succ] at h
    have h' := LinearMap.congr_fun h a
    rw [AlgHom.toLinearMap_apply] at h'
    rw [h', LinearMap.convMul_apply, ← PDivisibleGroup.Hopf.toLinearMap_nsmulAlgHom, WithConv.ofConv_toConv]
  rw [h1]
  generalize Coalgebra.comul (R := 𝓞) a = z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y =>
    rw [TensorProduct.map_tmul, LinearMap.mul'_apply, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.lmul'_apply_tmul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

include hπX hπΔ in
omit [Fact p.Prime] in

private theorem apply_nthSeries_eq_nsmulAlgHom (hπε : ∀ i, Coalgebra.counit (R := 𝓞) (π (X i)) = 0) :
    ∀ (n : ℕ) (i : Fin d), π (F.nthSeries n i) = PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 R n (π (X i))
  | 0, i => by
    rw [MvFormalGroup.nthSeries_zero, map_zero, PDivisibleGroup.Hopf.nsmulAlgHom_zero_apply, hπε, map_zero]
  | n + 1, i => by

    set Ψ : R ⊗[𝓞] R →ₐ[𝓞] R := (Algebra.TensorProduct.lmul' 𝓞 (S := R)).comp
      (Algebra.TensorProduct.map (PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 R n) (AlgHom.id 𝓞 R)) with hΨ
    have hR : PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 R (n + 1) (π (X i)) =
        MvFormalGroup.adicEval (Ideal.span {(p : R)})
          (Sum.elim (fun j => π (F.nthSeries n j)) (fun j => π (X j))) (F.toPowerSeries i) := by
      rw [nsmulAlgHom_succ_apply, hπΔ, ← hΨ,
        MvFormalGroup.map_adicEval (R := 𝓞) (Ideal.span {(p : R ⊗[𝓞] R)}) (Ideal.span {(p : R)}) Ψ
          (Submodule.fg_span_singleton _) ?_ ?_ (F.toPowerSeries i)]
      · congr 1
        funext s
        rcases s with j | j
        · rw [Sum.elim_inl, Sum.elim_inl, hΨ, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
            AlgHom.id_apply, Algebra.TensorProduct.lmul'_apply_tmul, mul_one,
            apply_nthSeries_eq_nsmulAlgHom hπε n j]
        · rw [Sum.elim_inr, Sum.elim_inr, hΨ, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
            AlgHom.id_apply, Algebra.TensorProduct.lmul'_apply_tmul, map_one, one_mul]
      · intro s hs
        obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hs
        refine Ideal.le_radical ?_
        rw [map_mul, map_natCast]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
      · rintro (j | j)
        · rw [Sum.elim_inl]
          exact map_mem_radical p (Algebra.TensorProduct.includeLeft : R →ₐ[𝓞] R ⊗[𝓞] R) (hπX j)
        · rw [Sum.elim_inr]
          exact map_mem_radical p (Algebra.TensorProduct.includeRight : R →ₐ[𝓞] R ⊗[𝓞] R) (hπX j)

    have hL : π (F.nthSeries (n + 1) i) =
        MvFormalGroup.adicEval (Ideal.span {(p : R)})
          (Sum.elim (fun j => π (F.nthSeries n j)) (fun j => π (X j))) (F.toPowerSeries i) := by
      rw [MvFormalGroup.nthSeries_succ, apply_eq_adicEval p R π hπX,
        MvFormalGroup.adicEval_subst (R := 𝓞) (Ideal.span {(p : R)}) (fun j => hπX j) (hasSubst_nthSeries F n)]
      congr 1
      funext s
      rcases s with j | j
      · rw [Sum.elim_inl, Sum.elim_inl, apply_eq_adicEval p R π hπX]
      · rw [Sum.elim_inr, Sum.elim_inr, MvFormalGroup.adicEval_X]
    rw [hL, hR]

omit [Fact p.Prime] [IsAdicComplete (Ideal.span {(p : R)}) R]
  [IsAdicComplete (Ideal.span {(p : R ⊗[𝓞] R)}) (R ⊗[𝓞] R)] in

private theorem counit_apply_eq_constantCoeff (G : MvPowerSeries (Fin d) 𝓞)
    (hπε : ∀ i, Coalgebra.counit (R := 𝓞) (π (X i)) = 0) :
    Coalgebra.counit (R := 𝓞) (π G) = MvPowerSeries.constantCoeff G := by
  let κ : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] 𝓞 :=
    { MvPowerSeries.constantCoeff with commutes' := fun c => MvPowerSeries.constantCoeff_C c }
  have h1 := MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical (⊥ : Ideal 𝓞)
    ((Bialgebra.counitAlgHom 𝓞 R).comp π) (fun s => by
      rw [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, hπε]; exact Ideal.zero_mem _) G
  have h2 := MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical (⊥ : Ideal 𝓞) κ
    (fun s => by
      change MvPowerSeries.constantCoeff (X s) ∈ _
      rw [constantCoeff_X]; exact Ideal.zero_mem _) G
  rw [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply] at h1
  rw [h1]
  change _ = κ G
  rw [h2]
  congr 1
  funext s
  rw [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, hπε]
  change (0 : 𝓞) = MvPowerSeries.constantCoeff (X s)
  rw [constantCoeff_X]

include hπX hπΔ in
omit [Fact p.Prime] in

private theorem torsionIdeal_eq_map_span_nthSeries (hπ : Function.Surjective π)
    (hπε : ∀ i, Coalgebra.counit (R := 𝓞) (π (X i)) = 0) (n : ℕ) :
    PDivisibleGroup.Hopf.torsionIdeal 𝓞 R n =
      Ideal.map π (Ideal.span (Set.range (F.nthSeries n))) := by

  have haug : PDivisibleGroup.Hopf.augIdeal 𝓞 R =
      Ideal.map π (Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) 𝓞))) := by
    apply le_antisymm
    · intro a ha
      obtain ⟨G, rfl⟩ := hπ a
      rw [PDivisibleGroup.Hopf.mem_augIdeal_iff, counit_apply_eq_constantCoeff R π G hπε] at ha
      refine Ideal.mem_map_of_mem _ ?_
      have := MvPowerSeries.mem_pow_span_X_of_coeff_eq_zero 1 G (fun m hm => by
        have hm0 : m = 0 := (Finsupp.degree_eq_zero_iff m).1 (by omega)
        rw [hm0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
        exact ha)
      rwa [pow_one] at this
    · rw [Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact (PDivisibleGroup.Hopf.mem_augIdeal_iff 𝓞 R _).2 (hπε i)
  rw [PDivisibleGroup.Hopf.torsionIdeal, haug, Ideal.map_span, Ideal.map_span, Ideal.map_span, Set.image_image,
    ← Set.range_comp, ← Set.range_comp]
  congr 2
  funext i
  exact (apply_nthSeries_eq_nsmulAlgHom p R π hπX F hπΔ hπε n i).symm

end Level

end TorsionLevelLemmas

section Main

theorem ker_eq_span_nthSeries_and_finrank
    (p : ℕ) [Fact p.Prime] (h : ℕ)
    (G : ℕ → Type v) [∀ v, CommRing (G v)] [∀ v, HopfAlgebra (ZMod p) (G v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)]
    (s : ∀ v, G (v + 1) →ₐc[ZMod p] G v) (hs : ∀ v, Function.Surjective (s v))
    (hrankG : ∀ v, Module.finrank (ZMod p) (G v) = p ^ (v * h))
    (hkerG : ∀ v, RingHom.ker (s v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (G (v + 1)) (p ^ v))
    (hconn : ∀ v, IsLocalRing (G v))
    {d : ℕ} (Φ : MvFormalGroup d (ZMod p)) (_hΦ : Φ.IsComm)
    (κ : ∀ v, MvPowerSeries (Fin d) (ZMod p) →ₐ[ZMod p] G v)
    (hκsurj : ∀ v, Function.Surjective (κ v))
    (hκcomp : ∀ v, (s v : G (v + 1) →ₐ[ZMod p] G v).comp (κ (v + 1)) = κ v)
    (hκε : ∀ v i, Coalgebra.counit (R := ZMod p) (κ v (X i)) = 0)
    (hκrad : ∀ v i, κ v (X i) ∈ (Ideal.span {(p : G v)}).radical)
    (_hκeval : ∀ v F, κ v F = MvFormalGroup.adicEval (Ideal.span {(p : G v)}) (fun i => κ v (X i)) F)
    (_hκinj : ∀ F, (∀ v, κ v F = 0) → F = 0)
    (_hκjs : ∀ z : ∀ v, G v, (∀ v, s v (z (v + 1)) = z v) → ∃ F, ∀ v, κ v F = z v)
    (hκker0 : ∀ N : ℕ, ∃ v, RingHom.ker (κ v) ≤
      (Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) (ZMod p)))) ^ N)
    (hκcomul : ∀ v i, Coalgebra.comul (R := ZMod p) (κ v (X i)) =
        MvFormalGroup.adicEval (Ideal.span {(p : G v ⊗[ZMod p] G v)})
          (Sum.elim (fun j => κ v (X j) ⊗ₜ[ZMod p] (1 : G v)) (fun j => (1 : G v) ⊗ₜ[ZMod p] κ v (X j)))
          (Φ.toPowerSeries i)) :
    (∀ v, RingHom.ker (κ v) = Ideal.span (Set.range (Φ.nthSeries (p ^ v)))) ∧
      Module.finrank (ZMod p)
        (MvPowerSeries (Fin d) (ZMod p) ⧸ Ideal.span (Set.range (Φ.nthSeries p))) = p ^ h := by
  classical

  have hp0 : ∀ v, (p : G v) = 0 := fun v => by
    rw [← map_natCast (algebraMap (ZMod p) (G v)) p, ZMod.natCast_self, map_zero]
  have hp0' : ∀ v, (p : G v ⊗[ZMod p] G v) = 0 := fun v => by
    rw [← map_natCast (algebraMap (ZMod p) (G v ⊗[ZMod p] G v)) p, ZMod.natCast_self, map_zero]
  haveI : ∀ v, IsAdicComplete (Ideal.span {(p : G v)}) (G v) := fun v => by
    rw [Ideal.span_singleton_eq_bot.2 (hp0 v)]; infer_instance
  haveI : ∀ v, IsAdicComplete (Ideal.span {(p : G v ⊗[ZMod p] G v)}) (G v ⊗[ZMod p] G v) := fun v => by
    rw [Ideal.span_singleton_eq_bot.2 (hp0' v)]; infer_instance

  obtain ⟨T, hT0, hTsucc, hTsurj, hTker, hpv, -⟩ :=
    PDivisibleGroup.Hopf.exists_forall_comp_transition_surjective_ker_eq_torsionIdeal p h G s hs hrankG hkerG

  have hJ : ∀ v, Ideal.span (Set.range (Φ.nthSeries (p ^ v))) ≤ RingHom.ker (κ v) := by
    intro v
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, TorsionLevelLemmas.apply_nthSeries_eq_nsmulAlgHom p (G v) (κ v) (hκrad v) Φ (hκcomul v) (hκε v), hpv v,
      AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, hκε, map_zero]

  haveI : IsNoetherianRing (MvPowerSeries (Fin d) (ZMod p)) := MvPowerSeries.isNoetherianRing_of_finite
  have hXm : Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) (ZMod p))) ≤
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) (ZMod p)) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact (IsLocalRing.mem_maximalIdeal _).2 fun hu => not_isUnit_zero
      (by rwa [MvPowerSeries.isUnit_iff_constantCoeff, constantCoeff_X] at hu)
  have hanti : Antitone fun w => RingHom.ker (κ w) := by
    refine antitone_nat_of_succ_le fun w => ?_
    intro F hF
    rw [RingHom.mem_ker] at hF ⊢
    rw [← hκcomp w, AlgHom.comp_apply, hF, map_zero]
  have hK : ∀ v, RingHom.ker (κ v) = Ideal.span (Set.range (Φ.nthSeries (p ^ v))) := by
    intro v
    refine le_antisymm ?_ (hJ v)
    set A := MvPowerSeries (Fin d) (ZMod p) with hA
    set J : Ideal A := Ideal.span (Set.range (Φ.nthSeries (p ^ v))) with hJdef

    have hTκ : ∀ w, ((T v w : G (v + w) →ₐc[ZMod p] G v) : G (v + w) →ₐ[ZMod p] G v).comp (κ (v + w)) =
        κ v := by
      intro w
      induction w with
      | zero => rw [hT0]; rfl
      | succ w ih =>
        rw [hTsucc, ← ih, ← hκcomp (v + w)]
        rfl
    have hkv : ∀ w, RingHom.ker (κ v) = J ⊔ RingHom.ker (κ (v + w)) := by
      intro w
      have h1 : RingHom.ker (κ v) =
          Ideal.comap (κ (v + w)) (RingHom.ker (T v w : G (v + w) →ₐc[ZMod p] G v)) := by
        rw [← hTκ w]
        ext F
        simp only [RingHom.mem_ker, Ideal.mem_comap, AlgHom.comp_apply]
        rfl
      rw [h1, hTker, TorsionLevelLemmas.torsionIdeal_eq_map_span_nthSeries p (G (v + w)) (κ (v + w))
        (hκrad (v + w)) Φ (hκcomul (v + w)) (hκsurj (v + w)) (hκε (v + w)) (p ^ v),
        Ideal.comap_map_of_surjective _ (hκsurj (v + w)), ← RingHom.ker_eq_comap_bot]

    intro F hF
    have hFN : ∀ N : ℕ, F ∈ J ⊔ IsLocalRing.maximalIdeal A ^ N := by
      intro N
      obtain ⟨w, hw⟩ := hκker0 N
      have hF' : F ∈ RingHom.ker (κ v) := hF
      rw [hkv w] at hF'
      have hle : RingHom.ker (κ (v + w)) ≤ IsLocalRing.maximalIdeal A ^ N :=
        le_trans (le_trans (hanti (Nat.le_add_left w v)) hw) (Ideal.pow_right_mono hXm N)
      exact (sup_le_sup_left hle J) hF'

    have hKrull : (⨅ N : ℕ, J ⊔ IsLocalRing.maximalIdeal A ^ N) = J := by
      refine le_antisymm ?_ (le_iInf fun N => le_sup_left)
      intro F hF
      have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := A ⧸ J)
        (I := IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal.isMaximal A).ne_top
      have hmk : J.mkQ F ∈ (⨅ N : ℕ, IsLocalRing.maximalIdeal A ^ N • (⊤ : Submodule A (A ⧸ J))) := by
        refine (Submodule.mem_iInf _).2 fun N => ?_
        obtain ⟨j, hj, m, hm, rfl⟩ := Submodule.mem_sup.1 ((Submodule.mem_iInf _).1 hF N)
        have hj0 : J.mkQ j = 0 := (Submodule.Quotient.mk_eq_zero J).2 hj
        rw [map_add, hj0, zero_add]
        have hm' : m ∈ IsLocalRing.maximalIdeal A ^ N • (⊤ : Submodule A A) := by
          simpa only [smul_eq_mul, mul_one] using
            Submodule.smul_mem_smul hm (Submodule.mem_top : (1 : A) ∈ (⊤ : Submodule A A))
        have h2 := Submodule.mem_map_of_mem (f := J.mkQ) hm'
        rwa [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at h2
      rw [hbot, Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hmk
      exact hmk
    rw [← hKrull]
    exact Ideal.mem_iInf.2 hFN
  refine ⟨hK, ?_⟩

  have hK1 : Ideal.span (Set.range (Φ.nthSeries p)) = RingHom.ker (κ 1) := by
    rw [hK 1, pow_one]
  have e : (MvPowerSeries (Fin d) (ZMod p) ⧸ Ideal.span (Set.range (Φ.nthSeries p))) ≃ₐ[ZMod p] G 1 :=
    (Ideal.quotientEquivAlgOfEq (ZMod p) hK1).trans (Ideal.quotientKerAlgEquivOfSurjective (hκsurj 1))
  rw [e.toLinearEquiv.finrank_eq, hrankG 1, one_mul]

end Main

end CoordKerFin

open scoped TensorProduct
open MvPowerSeries

namespace CoordMain

theorem isAdicComplete_zmodp (p : ℕ) : IsAdicComplete (Ideal.span {(p : ZMod p)}) (ZMod p) := by
  rw [ZMod.natCast_self, Ideal.span_singleton_eq_bot.mpr rfl]
  infer_instance

theorem ker_algebraMap_zmodp (p : ℕ) :
    RingHom.ker (algebraMap (ZMod p) (ZMod p)) = Ideal.span {(p : ZMod p)} := by
  rw [ZMod.natCast_self, Ideal.span_singleton_eq_bot.mpr rfl]
  ext x
  simp [RingHom.mem_ker]

theorem solutionPlus
    (p : ℕ) [Fact p.Prime] (h : ℕ)
    (G : ℕ → Type v) [∀ v, CommRing (G v)] [∀ v, HopfAlgebra (ZMod p) (G v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)]
    (s : ∀ v, G (v + 1) →ₐc[ZMod p] G v) (hs : ∀ v, Function.Surjective (s v))
    (hrankG : ∀ v, Module.finrank (ZMod p) (G v) = p ^ (v * h))
    (hkerG : ∀ v, RingHom.ker (s v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (G (v + 1)) (p ^ v))
    (hconn : ∀ v, IsLocalRing (G v)) :
    ∃ (d : ℕ) (Φ : MvFormalGroup d (ZMod p)) (_ : Φ.IsComm)
      (κ : ∀ v, MvPowerSeries (Fin d) (ZMod p) →ₐ[ZMod p] G v),
      (∀ v, Function.Surjective (κ v)) ∧
      (∀ v, RingHom.ker (κ v) = Ideal.span (Set.range (Φ.nthSeries (p ^ v)))) ∧
      (∀ v, (s v : G (v + 1) →ₐ[ZMod p] G v).comp (κ (v + 1)) = κ v) ∧
      (∀ v i, Coalgebra.counit (R := ZMod p) (κ v (X i)) = 0) ∧
      (∀ v i, κ v (X i) ∈ (Ideal.span {(p : G v)}).radical) ∧
      (∀ v F, κ v F = MvFormalGroup.adicEval (Ideal.span {(p : G v)}) (fun i => κ v (X i)) F) ∧
      (∀ v i, Coalgebra.comul (R := ZMod p) (κ v (X i)) =
        MvFormalGroup.adicEval (Ideal.span {(p : G v ⊗[ZMod p] G v)})
          (Sum.elim (fun j => κ v (X j) ⊗ₜ[ZMod p] (1 : G v)) (fun j => (1 : G v) ⊗ₜ[ZMod p] κ v (X j)))
          (Φ.toPowerSeries i)) ∧
      Module.finrank (ZMod p)
        (MvPowerSeries (Fin d) (ZMod p) ⧸ Ideal.span (Set.range (Φ.nthSeries p))) = p ^ h ∧
      d = Module.finrank (ZMod p) (PDivisibleGroup.Hopf.augIdeal (ZMod p) (G 1)).Cotangent ∧
      (∀ N : ℕ, ∃ v, RingHom.ker (κ v) ≤
        (Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) (ZMod p)))) ^ N) ∧
      (∀ F, (∀ v, κ v F = 0) → F = 0) ∧
      (∀ z : ∀ v, G v, (∀ v, s v (z (v + 1)) = z v) → ∃ F, ∀ v, κ v F = z v) := by
  classical
  haveI hO : IsAdicComplete (Ideal.span {(p : ZMod p)}) (ZMod p) := isAdicComplete_zmodp p
  have hp0 : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self p
  have hker := ker_algebraMap_zmodp p
  haveI hc1 : ∀ v, IsAdicComplete (Ideal.span {(p : G v)}) (G v) := fun v =>
    IsAdicComplete.of_module_finite_free_span_natCast (𝓞 := ZMod p) p (G v)

  obtain ⟨d, π₀, hd, hsurj₀, hcomp₀, hε₀, hnil₀, hker₀, hinj₀, hjs₀⟩ :=
    PDivisibleGroup.exists_surjective_mvPowerSeries_comp_eq_of_isLocalRing_zmodp p h G s hs hrankG hkerG hconn

  obtain ⟨hxt, hxrad, hxsurj, hxker⟩ :=
    CoordTransfer.specialFibre_coordinates_of_tower p G (fun v => (s v : G (v + 1) →ₐ[ZMod p] G v)) π₀
      hcomp₀ hnil₀ hsurj₀ hker₀
  have hxε : ∀ v i, Coalgebra.counit (R := ZMod p) (π₀ v (X i)) = 0 := hε₀

  obtain ⟨Φ, hΦ, π, hπX, hπsurj, hπcomp, hπrad, hπeval, hπinj, hπjs, hπε, hπcomul⟩ :=
    CoordLaw.law (𝓞 := ZMod p) p hp0 hker G s d (fun v i => π₀ v (X i)) hxt hxε hxrad hxsurj hxker

  have hππ₀ : ∀ v, π v = π₀ v := by
    intro v
    apply AlgHom.ext
    intro F
    rw [hπeval v F, MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical
      (Ideal.span {(p : G v)}) (π₀ v) (fun i => (hxrad v i)) F]
    congr 1
    funext i
    exact hπX v i
  have hker0' : ∀ N : ℕ, ∃ v, RingHom.ker (π v) ≤
      (Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) (ZMod p)))) ^ N := by
    intro N
    obtain ⟨v, hv⟩ := hker₀ N
    exact ⟨v, by rw [hππ₀ v]; exact hv⟩
  have hπjs' : ∀ z : ∀ v, G v, (∀ v, s v (z (v + 1)) = z v) → ∃ F, ∀ v, π v F = z v := hπjs

  obtain ⟨hkerΦ, hfin⟩ :=
    CoordKerFin.ker_eq_span_nthSeries_and_finrank p h G s hs hrankG hkerG hconn Φ hΦ π hπsurj hπcomp hπε hπrad
      hπeval hπinj hπjs' hker0' hπcomul
  exact ⟨d, Φ, hΦ, π, hπsurj, hkerΦ, hπcomp, hπε, hπrad, hπeval, hπcomul, hfin, hd, hker0', hπinj, hπjs'⟩

end CoordMain

open CoordMain in

theorem solution
    (p : ℕ) [Fact p.Prime] (h : ℕ)
    (G : ℕ → Type v) [∀ v, CommRing (G v)] [∀ v, HopfAlgebra (ZMod p) (G v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)]
    (s : ∀ v, G (v + 1) →ₐc[ZMod p] G v) (hs : ∀ v, Function.Surjective (s v))
    (hrankG : ∀ v, Module.finrank (ZMod p) (G v) = p ^ (v * h))
    (hkerG : ∀ v, RingHom.ker (s v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (G (v + 1)) (p ^ v))
    (hconn : ∀ v, IsLocalRing (G v)) :
    ∃ (d : ℕ) (Φ : MvFormalGroup d (ZMod p)) (_ : Φ.IsComm)
      (κ : ∀ v, MvPowerSeries (Fin d) (ZMod p) →ₐ[ZMod p] G v),
      (∀ v, Function.Surjective (κ v)) ∧
      (∀ v, RingHom.ker (κ v) = Ideal.span (Set.range (Φ.nthSeries (p ^ v)))) ∧
      (∀ v, (s v : G (v + 1) →ₐ[ZMod p] G v).comp (κ (v + 1)) = κ v) ∧
      (∀ v i, Coalgebra.counit (R := ZMod p) (κ v (X i)) = 0) ∧
      (∀ v i, κ v (X i) ∈ (Ideal.span {(p : G v)}).radical) ∧
      (∀ v F, κ v F = MvFormalGroup.adicEval (Ideal.span {(p : G v)}) (fun i => κ v (X i)) F) ∧
      (∀ v i, Coalgebra.comul (R := ZMod p) (κ v (X i)) =
        MvFormalGroup.adicEval (Ideal.span {(p : G v ⊗[ZMod p] G v)})
          (Sum.elim (fun j => κ v (X j) ⊗ₜ[ZMod p] (1 : G v)) (fun j => (1 : G v) ⊗ₜ[ZMod p] κ v (X j)))
          (Φ.toPowerSeries i)) ∧
      Module.finrank (ZMod p)
        (MvPowerSeries (Fin d) (ZMod p) ⧸ Ideal.span (Set.range (Φ.nthSeries p))) = p ^ h ∧
      d = Module.finrank (ZMod p) (PDivisibleGroup.Hopf.augIdeal (ZMod p) (G 1)).Cotangent ∧
      (∀ N : ℕ, ∃ v, RingHom.ker (κ v) ≤
        (Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) (ZMod p)))) ^ N) ∧
      (∀ F, (∀ v, κ v F = 0) → F = 0) ∧
      (∀ z : ∀ v, G v, (∀ v, s v (z (v + 1)) = z v) → ∃ F, ∀ v, κ v F = z v) :=
  CoordMain.solutionPlus p h G s hs hrankG hkerG hconn

end S_PDivisibleGroup_exists_mvFormalGroup_ker_eq_span_nthSeries_jointly_injective_surjective_of_isLocalRing_zmodp
end P2MW
export P2MW.S_PDivisibleGroup_exists_mvFormalGroup_ker_eq_span_nthSeries_jointly_injective_surjective_of_isLocalRing_zmodp (solution)
