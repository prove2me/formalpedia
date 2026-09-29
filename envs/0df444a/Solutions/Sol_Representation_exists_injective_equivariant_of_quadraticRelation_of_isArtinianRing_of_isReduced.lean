-- Prove2me | solution 1 for Representation.exists_injective_equivariant_of_quadraticRelation_of_isArtinianRing_of_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/e6994e36-904a-5eb0-880d-f2735d7964d9

import Mathlib
import Theorems.Thm_Representation_exists_blrDecomposition_of_spanTop_of_quadraticAnnihilation
import Theorems.Thm_Representation_det_eq_of_sq_sub_trace_smul_add_smul_one_eq_zero
import Theorems.Thm_LinearMap_baseChange_free_finrank_two_and_span_eq_top_and_trace_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Representation_exists_injective_equivariant_of_quadraticRelation_of_isArtinianRing_of_isReduced

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped TensorProduct

theorem BLRFaceAp.perFactor
    {k : Type} [CommRing k] {K : Type} [Field K] [Algebra k K] (h2 : (2 : K) ≠ 0)
    {G : Type} [Group G]
    {V : Type} [AddCommGroup V] [Module k V] [Module.Free k V] [Module.Finite k V]
    (hV : Module.finrank k V = 2)
    (ρV : G →* Module.End k V) (hspan : Submodule.span k (Set.range ⇑ρV) = ⊤)
    {M : Type} [AddCommGroup M] [Module k M] [Module.Finite k M]
    (hM : Nontrivial (K ⊗[k] M))
    (ρM : G →* Module.End k M) (d : G →* kˣ)
    (hrel : ∀ g : G,
      ρM g * ρM g - (LinearMap.trace k V (ρV g)) • ρM g + ((d g : kˣ) : k) • (1 : Module.End k M) = 0) :
    ∃ ψ : V →ₗ[k] (K ⊗[k] M),
      (∀ (g : G) (v : V), ψ (ρV g v) = (ρM g).baseChange K (ψ v)) ∧
      (∀ v : V, ψ v = 0 → ((1 : K) ⊗ₜ[k] v : K ⊗[k] V) = 0) := by
  classical
  haveI := hM
  obtain ⟨hVK, hspanK, htrK, hintK, -⟩ :=
    LinearMap.baseChange_free_finrank_two_and_span_eq_top_and_trace_eq (k := K) hV ρV hspan

  let ρVK : G →* Module.End K (K ⊗[k] V) :=
    { toFun := fun g => (ρV g).baseChange K
      map_one' := by rw [map_one]; exact LinearMap.baseChange_one k V
      map_mul' := fun g h => by rw [map_mul]; exact LinearMap.baseChange_mul _ _ }
  have hρVK : ∀ g, ρVK g = (ρV g).baseChange K := fun g => rfl
  let ρMK : G →* Module.End K (K ⊗[k] M) :=
    { toFun := fun g => (ρM g).baseChange K
      map_one' := by rw [map_one]; exact LinearMap.baseChange_one k M
      map_mul' := fun g h => by rw [map_mul]; exact LinearMap.baseChange_mul _ _ }
  have hρMK : ∀ g, ρMK g = (ρM g).baseChange K := fun g => rfl

  let dK : G →* Kˣ := (Units.map ((algebraMap k K : k →+* K) : k →* K)).comp d
  have hdK : ∀ g, ((dK g : Kˣ) : K) = algebraMap k K ((d g : kˣ) : k) := fun g => rfl

  have hrelK : ∀ g : G,
      ρMK g * ρMK g - (LinearMap.trace K (K ⊗[k] V) (ρVK g)) • ρMK g
        + ((dK g : Kˣ) : K) • (1 : Module.End K (K ⊗[k] M)) = 0 := by
    intro g
    have h := congrArg (LinearMap.baseChange K) (hrel g)
    rw [LinearMap.baseChange_zero, LinearMap.baseChange_add, LinearMap.baseChange_sub,
      LinearMap.baseChange_mul, LinearMap.baseChange_smul, LinearMap.baseChange_smul,
      LinearMap.baseChange_one] at h
    rw [hρVK, hρMK, htrK, hdK, algebraMap_smul, algebraMap_smul]
    exact h

  have hdet : ∀ g : G, LinearMap.det (ρVK g) = dK g :=
    Representation.det_eq_of_sq_sub_trace_smul_add_smul_one_eq_zero h2 hVK ρVK ρMK dK hrelK

  let b : Module.Basis (Fin 2) K (K ⊗[k] V) := Module.finBasisOfFinrankEq K (K ⊗[k] V) hVK
  let ρ : G →* Matrix (Fin 2) (Fin 2) K :=
    { toFun := fun g => LinearMap.toMatrix b b (ρVK g)
      map_one' := by rw [map_one]; exact LinearMap.toMatrix_one b
      map_mul' := fun g h => by rw [map_mul]; exact LinearMap.toMatrix_mul b (ρVK g) (ρVK h) }
  have hρ : ∀ g, ρ g = LinearMap.toMatrix b b (ρVK g) := fun g => rfl
  have hirr : Submodule.span K (Set.range (fun g : G => ρ g)) = ⊤ := by
    have hr : Set.range (fun g : G => ρ g)
        = ⇑(LinearMap.toMatrix b b).toLinearMap '' Set.range (fun g : G => (ρV g).baseChange K) := by
      ext A
      simp only [Set.mem_range, Set.mem_image, hρ, hρVK, LinearEquiv.coe_coe, exists_exists_eq_and]
    rw [hr, Submodule.span_image, hspanK, Submodule.map_top, LinearEquiv.range]
  have hann : ∀ g : G,
      ρMK g ^ 2 - Matrix.trace (ρ g) • ρMK g + (ρ g).det • (1 : K ⊗[k] M →ₗ[K] K ⊗[k] M) = 0 := by
    intro g
    rw [pow_two, hρ, ← LinearMap.trace_eq_matrix_trace K b, LinearMap.det_toMatrix b, hdet g]
    exact hrelK g
  obtain ⟨n, e, he⟩ :=
    Representation.exists_blrDecomposition_of_spanTop_of_quadraticAnnihilation ρ ρMK h2 hirr hann

  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · exfalso
      subst h0
      haveI : Subsingleton (K ⊗[k] M) := e.toEquiv.subsingleton
      exact false_of_nontrivial_of_subsingleton (K ⊗[k] M)
    · exact hpos
  let i0 : Fin n := ⟨0, hn⟩

  let φ : K ⊗[k] V →ₗ[K] K ⊗[k] M :=
    e.symm.toLinearMap ∘ₗ LinearMap.single K (fun _ : Fin n => Fin 2 → K) i0 ∘ₗ b.equivFun.toLinearMap
  have hφ : ∀ x : K ⊗[k] V, e (φ x) = Pi.single i0 (⇑(b.repr x)) := by
    intro x
    simp only [φ, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.apply_symm_apply,
      LinearMap.coe_single, Module.Basis.equivFun_apply]
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have h1 : Pi.single i0 (⇑(b.repr x)) = Pi.single (M := fun _ : Fin n => Fin 2 → K) i0 (⇑(b.repr y)) := by
      rw [← hφ, ← hφ, hxy]
    have h2' : ⇑(b.repr x) = ⇑(b.repr y) := Pi.single_injective (M := fun _ : Fin n => Fin 2 → K) (i := i0) h1
    exact b.repr.injective (DFunLike.coe_injective h2')
  have hφeq : ∀ (g : G) (x : K ⊗[k] V), φ (ρVK g x) = ρMK g (φ x) := by
    intro g x
    apply e.injective
    funext i
    rw [he, hφ, hφ]
    by_cases hi : i = i0
    · subst hi
      rw [Pi.single_eq_same, Pi.single_eq_same, hρ, LinearMap.toMatrix_mulVec_repr]
    · rw [Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hi, Matrix.mulVec_zero]

  refine ⟨(φ.restrictScalars k) ∘ₗ TensorProduct.mk k K V 1, ?_, ?_⟩
  · intro g v
    show φ ((1 : K) ⊗ₜ[k] ρV g v) = (ρM g).baseChange K (φ ((1 : K) ⊗ₜ[k] v))
    rw [← hintK, ← hρVK, hφeq, hρMK]
  · intro v hv
    exact hφinj (by simpa using hv)

theorem solution
    {k : Type} [CommRing k] [IsArtinianRing k] [IsReduced k] [Algebra ℚ k]
    {G : Type} [Group G]
    {V : Type} [AddCommGroup V] [Module k V] [Module.Free k V] [Module.Finite k V] (hV : Module.finrank k V = 2)
    (ρV : G →* Module.End k V) (hspan : Submodule.span k (Set.range ⇑ρV) = ⊤)
    {M : Type} [AddCommGroup M] [Module k M] [Module.Finite k M]
    (hfaith : ∀ x : k, (∀ m : M, x • m = 0) → x = 0)
    (ρM : G →* Module.End k M) (d : G →* kˣ)
    (hrel : ∀ g : G,
      ρM g * ρM g - (LinearMap.trace k V (ρV g)) • ρM g + ((d g : kˣ) : k) • (1 : Module.End k M) = 0) :
    ∃ j : V →ₗ[k] M, Function.Injective j ∧ ∀ (g : G) (v : V), j (ρV g v) = ρM g (j v) := by
  classical
  haveI : Fintype (MaximalSpectrum k) := Fintype.ofFinite _
  letI : ∀ P : MaximalSpectrum k, Field (k ⧸ P.asIdeal) := fun P => Ideal.Quotient.field P.asIdeal

  have h2 : ∀ P : MaximalSpectrum k, (2 : k ⧸ P.asIdeal) ≠ 0 := by
    intro P h
    apply (two_ne_zero : (2 : ℚ) ≠ 0)
    apply (algebraMap ℚ (k ⧸ P.asIdeal)).injective
    rw [map_ofNat, map_zero]
    exact h

  have hnt : ∀ P : MaximalSpectrum k, Nontrivial ((k ⧸ P.asIdeal) ⊗[k] M) := by
    intro P
    by_contra hc
    rw [not_nontrivial_iff_subsingleton] at hc
    haveI : Subsingleton (M ⧸ (P.asIdeal • ⊤ : Submodule k M)) :=
      (TensorProduct.quotTensorEquivQuotSMul M P.asIdeal).symm.toEquiv.subsingleton
    have htop : (P.asIdeal • ⊤ : Submodule k M) = ⊤ :=
      (Submodule.Quotient.subsingleton_iff (p := (P.asIdeal • ⊤ : Submodule k M))).mp inferInstance
    obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
      P.asIdeal (⊤ : Submodule k M) Module.Finite.fg_top (by rw [htop])
    have hr0 : r = 0 := hfaith r (fun m => hr m trivial)
    rw [hr0, zero_sub] at hr1
    exact P.isMaximal.ne_top (Ideal.eq_top_of_isUnit_mem _ hr1 isUnit_one.neg)

  have key := fun P : MaximalSpectrum k =>
    BLRFaceAp.perFactor (K := k ⧸ P.asIdeal) (h2 P) hV ρV hspan (hnt P) ρM d hrel
  choose ψ hψeq hψker using key

  have hcop : Pairwise (Function.onFun IsCoprime fun P : MaximalSpectrum k => P.asIdeal) :=
    fun P Q hPQ => MaximalSpectrum.isCoprime_of_ne hPQ
  have hinf : (⨅ P : MaximalSpectrum k, P.asIdeal) = ⊥ := by
    have h := IsArtinianRing.nilradical_eq_iInf k
    rw [nilradical_eq_zero, Submodule.zero_eq_bot] at h
    exact h.symm
  let θ : M →ₗ[k] (∀ P : MaximalSpectrum k, (k ⧸ P.asIdeal) ⊗[k] M) :=
    LinearMap.pi fun P => TensorProduct.mk k (k ⧸ P.asIdeal) M 1
  have hθ : ∀ (m : M) (P : MaximalSpectrum k), θ m P = (1 : k ⧸ P.asIdeal) ⊗ₜ[k] m := fun m P => rfl
  have hθsurj : Function.Surjective θ := Ideal.pi_tensorProductMk_quotient_surjective M _ hcop
  have hθinj : Function.Injective θ := by
    rw [← LinearMap.ker_eq_bot]
    show LinearMap.ker (LinearMap.pi fun P : MaximalSpectrum k => TensorProduct.mk k (k ⧸ P.asIdeal) M 1) = ⊥
    rw [Ideal.ker_tensorProductMk_quotient M _ hcop, hinf, Submodule.bot_smul]
  have hθVinj : Function.Injective
      (LinearMap.pi fun P : MaximalSpectrum k => TensorProduct.mk k (k ⧸ P.asIdeal) V 1) := by
    rw [← LinearMap.ker_eq_bot, Ideal.ker_tensorProductMk_quotient V _ hcop, hinf, Submodule.bot_smul]
  let Θ : M ≃ₗ[k] (∀ P : MaximalSpectrum k, (k ⧸ P.asIdeal) ⊗[k] M) :=
    LinearEquiv.ofBijective θ ⟨hθinj, hθsurj⟩
  have hΘ : ∀ m : M, Θ m = θ m := fun m => rfl
  let Ψ : V →ₗ[k] (∀ P : MaximalSpectrum k, (k ⧸ P.asIdeal) ⊗[k] M) := LinearMap.pi ψ
  have hΨ : ∀ (v : V) (P : MaximalSpectrum k), Ψ v P = ψ P v := fun v P => rfl
  refine ⟨Θ.symm.toLinearMap ∘ₗ Ψ, ?_, ?_⟩
  ·
    refine Θ.symm.injective.comp ?_
    intro v w hvw
    rw [← sub_eq_zero] at hvw ⊢
    rw [← map_sub] at hvw
    apply hθVinj
    rw [map_zero]
    funext P
    exact hψker P (v - w) (by rw [← hΨ, hvw]; rfl)
  ·
    intro g v
    show Θ.symm (Ψ (ρV g v)) = ρM g (Θ.symm (Ψ v))
    rw [LinearEquiv.symm_apply_eq, hΘ]
    funext P
    rw [hΨ, hψeq, hθ, ← LinearMap.baseChange_tmul, ← hθ, ← hΘ, LinearEquiv.apply_symm_apply, hΨ]

end S_Representation_exists_injective_equivariant_of_quadraticRelation_of_isArtinianRing_of_isReduced
end P2MW
export P2MW.S_Representation_exists_injective_equivariant_of_quadraticRelation_of_isArtinianRing_of_isReduced (solution)
