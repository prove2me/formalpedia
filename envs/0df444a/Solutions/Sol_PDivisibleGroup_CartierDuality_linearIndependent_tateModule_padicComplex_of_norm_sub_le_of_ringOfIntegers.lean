-- Prove2me | solution 1 for PDivisibleGroup.CartierDuality.linearIndependent_tateModule_padicComplex_of_norm_sub_le_of_ringOfIntegers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/6f3c3d44-e3a9-5adc-bee5-87c00405e6e5

import Mathlib
import Definitions.Def_PadicComplex_GaloisAction
import Definitions.Def_PDivisibleGroup_CharacterDifferential
import Definitions.Def_PDivisibleGroup_CompletedPoints
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Theorems.Thm_PDivisibleGroup_nonempty_basis_cotangentModule_of_hasDimension
import Theorems.Thm_PadicAlgCl_isIntegral_padicInt_iff_norm_le_one
import Theorems.Thm_PadicAlgCl_ringOfIntegers_finite_and_isDiscreteValuationRing_and_isAdicComplete
import Theorems.Thm_PDivisibleGroup_CartierDuality_exists_addMonoidHom_tangentSpace_cpoints_pair_eq_sum_pow_of_ker_cotangentModuleProj_eq
import Theorems.Thm_PDivisibleGroup_CartierDuality_cpoints_eq_zero_of_forall_pair_eq_one_of_forall_mem_range_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_CartierDuality_linearIndependent_tateModule_padicComplex_of_norm_sub_le_of_ringOfIntegers
p2m_attr_erase "instance" "PrimaryTorsion.instSMul PrimaryTorsion.instModule"
p2m_attr_erase "simp" "PrimaryTorsion.coe_ofTateModule PrimaryTorsion.coe_map HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul"

set_option autoImplicit false

open PDivisibleGroup Filter Topology
open scoped TensorProduct

namespace PDivINJK

variable (p : ℕ) [Fact p.Prime]

section Generic

variable {R : Type} [CommRing R] [Algebra R (PadicAlgCl p)]

noncomputable abbrev OR (R : Type) [CommRing R] [Algebra R (PadicAlgCl p)] : Subalgebra R (PadicAlgCl p) :=
  integralClosure R (PadicAlgCl p)

noncomputable def ι (R : Type) [CommRing R] [Algebra R (PadicAlgCl p)] : OR p R →+* ℂ_[p] :=
  (algebraMap (PadicAlgCl p) ℂ_[p]).comp (OR p R).val.toRingHom

theorem ι_apply (c : OR p R) : ι p R c = ((c : PadicAlgCl p) : ℂ_[p]) := rfl

noncomputable def κ (R : Type) [CommRing R] [Algebra R (PadicAlgCl p)] (a : R) : ℂ_[p] :=
  ((algebraMap R (PadicAlgCl p) a : PadicAlgCl p) : ℂ_[p])

theorem norm_coe_p : ‖(p : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p]
  exact (PadicAlgCl.norm_extends (p := p) (p : ℚ_[p])).trans (Padic.norm_p (p := p))

theorem norm_coe_p_pow (v : ℕ) : ‖((p : PadicAlgCl p)) ^ v‖ = ((p : ℝ) ^ v)⁻¹ := by
  rw [norm_pow, norm_coe_p, inv_pow]

theorem mem_span_of_norm_ι_le (hval : ∀ x : PadicAlgCl p, ‖x‖ ≤ 1 → x ∈ OR p R)
    (v : ℕ) (c : OR p R) (hc : ‖ι p R c‖ ≤ (p : ℝ) ^ (-(v : ℤ))) :
    c ∈ Ideal.span {(p : OR p R) ^ v} := by
  have hp0 : (p : PadicAlgCl p) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpv0 : (p : PadicAlgCl p) ^ v ≠ 0 := pow_ne_zero _ hp0
  have hppos : (0 : ℝ) < (p : ℝ) ^ v := pow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) v

  have hc' : ‖(c : PadicAlgCl p)‖ ≤ ((p : ℝ) ^ v)⁻¹ := by
    rw [ι_apply, PadicComplex.norm_extends] at hc
    rwa [zpow_neg, zpow_natCast] at hc

  set d : PadicAlgCl p := (c : PadicAlgCl p) / (p : PadicAlgCl p) ^ v with hd
  have hdn : ‖d‖ ≤ 1 := by
    rw [hd, norm_div, norm_coe_p_pow, div_le_one (inv_pos.mpr hppos)]
    exact hc'
  refine Ideal.mem_span_singleton'.mpr ⟨⟨d, hval d hdn⟩, Subtype.ext ?_⟩
  change d * (((p : OR p R) ^ v : OR p R) : PadicAlgCl p) = (c : PadicAlgCl p)
  have hcoe : (((p : OR p R) ^ v : OR p R) : PadicAlgCl p) = (p : PadicAlgCl p) ^ v := by
    rw [SubmonoidClass.coe_pow]; rfl
  rw [hcoe, hd, div_mul_cancel₀ _ hpv0]

theorem span_pow_mono {i w : ℕ} (hiw : i ≤ w) :
    Ideal.span {(p : OR p R) ^ w} ≤ Ideal.span {(p : OR p R) ^ i} :=
  Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ hiw)

variable {h : ℕ} (G : PDivisibleGroup R p h) {n : ℕ}

noncomputable abbrev projS (v : ℕ) :
    OR p R ⊗[R] G.cotangentModule →ₗ[R] OR p R ⊗[R] G.Cotangent v :=
  (G.cotangentModuleProj v).lTensor (OR p R)

noncomputable def evalS (τ : G.tangentSpace R) : OR p R ⊗[R] G.cotangentModule →ₗ[R] OR p R :=
  (TensorProduct.rid R (OR p R)).toLinearMap ∘ₗ τ.lTensor (OR p R)

theorem evalS_apply (τ : G.tangentSpace R) (z : OR p R ⊗[R] G.cotangentModule) :
    evalS p G τ z = TensorProduct.rid R (OR p R) (τ.lTensor (OR p R) z) := rfl

theorem evalS_tmul (τ : G.tangentSpace R) (s : OR p R) (w : G.cotangentModule) :
    evalS p G τ (s ⊗ₜ[R] w) = τ w • s := by
  simp [evalS]

theorem evalS_add (τ τ' : G.tangentSpace R) : evalS p G (τ + τ') = evalS p G τ + evalS p G τ' := by
  refine TensorProduct.ext' fun s w => ?_
  rw [LinearMap.add_apply, evalS_tmul, evalS_tmul, evalS_tmul, LinearMap.add_apply, add_smul]

theorem evalS_smul (a : R) (τ : G.tangentSpace R) : evalS p G (a • τ) = a • evalS p G τ := by
  refine TensorProduct.ext' fun s w => ?_
  simp only [LinearMap.smul_apply, evalS_tmul, smul_eq_mul, mul_smul]

theorem evalS_zero : evalS p G (0 : G.tangentSpace R) = 0 := by
  refine TensorProduct.ext' fun s w => ?_
  rw [evalS_tmul, LinearMap.zero_apply, LinearMap.zero_apply, zero_smul]

theorem evalS_sum_smul (c : Fin n → R) (b : Module.Basis (Fin n) R G.cotangentModule)
    (z : OR p R ⊗[R] G.cotangentModule) :
    evalS p G (∑ j, c j • b.coord j) z = ∑ j, c j • evalS p G (b.coord j) z := by
  classical
  have key : ∀ s : Finset (Fin n),
      evalS p G (∑ j ∈ s, c j • b.coord j) z = ∑ j ∈ s, c j • evalS p G (b.coord j) z := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.sum_empty, evalS_zero, LinearMap.zero_apply]
    | insert j s hj ih =>
        rw [Finset.sum_insert hj, Finset.sum_insert hj, evalS_add, LinearMap.add_apply, ih, evalS_smul,
          LinearMap.smul_apply]
  exact key Finset.univ

theorem ι_smul (a : R) (s : OR p R) : ι p R (a • s) = κ p R a * ι p R s := by
  rw [Algebra.smul_def, map_mul, ι_apply, ι_apply, κ, Subalgebra.coe_algebraMap]

theorem evalS_mem_span (hval : ∀ x : PadicAlgCl p, ‖x‖ ≤ 1 → x ∈ OR p R)
    (hR1 : ∀ a : R, ‖algebraMap R (PadicAlgCl p) a‖ ≤ 1)
    (b : Module.Basis (Fin n) R G.cotangentModule) (c : Fin n → R)
    (dαv : Fin n → ℂ_[p]) (z : OR p R ⊗[R] G.cotangentModule) (v : ℕ)
    (hsum : ∑ j, κ p R (c j) * dαv j = 0)
    (hpin : ∀ j, ‖dαv j - ι p R (evalS p G (b.coord j) z)‖ ≤ (p : ℝ) ^ (-(v : ℤ))) :
    evalS p G (∑ j, c j • b.coord j) z ∈ Ideal.span {(p : OR p R) ^ v} := by
  refine mem_span_of_norm_ι_le p hval v _ ?_
  rw [evalS_sum_smul, map_sum]
  simp_rw [ι_smul]

  have h1 : ∑ j, κ p R (c j) * ι p R (evalS p G (b.coord j) z) =
      ∑ j, κ p R (c j) * (ι p R (evalS p G (b.coord j) z) - dαv j) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, hsum, sub_zero]
  rw [h1]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun j _ => ?_
  rw [norm_mul, norm_sub_rev]
  have hκ : ‖κ p R (c j)‖ ≤ 1 := by
    rw [κ, PadicComplex.norm_extends]
    exact hR1 (c j)
  calc ‖κ p R (c j)‖ * ‖dαv j - ι p R (evalS p G (b.coord j) z)‖ ≤ 1 * (p : ℝ) ^ (-(v : ℤ)) :=
        mul_le_mul hκ (hpin j) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

structure Tower : Prop where
  surj : ∀ v, Function.Surjective (G.cotangentModuleProj v)
  ker : ∀ v, LinearMap.ker (G.cotangentModuleProj v) = Ideal.span {(p : R) ^ v} • ⊤

theorem sum_range_mul_zero_pow {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (i : ℕ)
    (hi : i ≠ 0) (c : ℕ → A) (hc0 : c 0 = 1) :
    ∑ k ∈ Finset.range i, φ (c k) * (0 : B) ^ k = 1 := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
  rw [Finset.sum_range_succ']
  simp [hc0]

theorem eq_zero_of_forall_sum_eq_zero [Algebra ℤ_[p] R]
    (hval : ∀ x : PadicAlgCl p, ‖x‖ ≤ 1 → x ∈ OR p R)
    (hR1 : ∀ a : R, ‖algebraMap R (PadicAlgCl p) a‖ ≤ 1)
    (htf : ∀ x : R, (p : R) * x = 0 → x = 0)
    (hsep : ∀ x : R, (∀ i : ℕ, x ∈ Ideal.span {(p : R) ^ i}) → x = 0)
    {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')
    (hsurj : ∀ v, Function.Surjective (G.cotangentModuleProj v))
    (hker : ∀ v, LinearMap.ker (G.cotangentModuleProj v) =
      Ideal.span {(p : R) ^ v} • (⊤ : Submodule R G.cotangentModule))
    (hstep4 : ∀ g : G.CPoints R,
      (∀ (y : TateModule p (G'.Points (PadicAlgCl p))) (i w : ℕ), i ≤ w →
        ∀ (f : G.Point (OR p R ⧸ Ideal.span {(p : OR p R) ^ i}) w),
          G.pointsMkAdd _ w (Additive.ofMul f) =
            G.cpointsProj (OR p R) i (G.cpointsMap (Algebra.ofId R (OR p R)) g) →
        ∀ (ψ : G'.Point (OR p R) w),
          G'.pointsMkAdd (PadicAlgCl p) w (Additive.ofMul (G'.pointMap (OR p R).val w ψ)) =
            (y : ℕ → G'.Points (PadicAlgCl p)) w →
          D.pair _ w f (G'.pointMap (Ideal.Quotient.mkₐ R (Ideal.span {(p : OR p R) ^ i})) w ψ) = 1) →
      g = 0)
    (b : Module.Basis (Fin n) R G.cotangentModule)
    (dα : Fin n → (TateModule p (G'.Points (PadicAlgCl p)) →+ ℂ_[p]))
    (hdα : ∀ (j : Fin n) (y : TateModule p (G'.Points (PadicAlgCl p))) (v : ℕ) (ψ : G'.Point (OR p R) v),
        G'.pointsMkAdd (PadicAlgCl p) v (Additive.ofMul (G'.pointMap (OR p R).val v ψ)) =
          (y : ℕ → G'.Points (PadicAlgCl p)) v →
        ∀ z : OR p R ⊗[R] G.cotangentModule,
          (G.cotangentModuleProj v).lTensor (OR p R) z = D.charDiff (OR p R) v ψ →
          ‖dα j y - ((TensorProduct.rid R (OR p R) ((b.coord j).lTensor (OR p R) z) : PadicAlgCl p) : ℂ_[p])‖ ≤
            (p : ℝ) ^ (-(v : ℤ)))
    (c : Fin n → R) (hc : ∀ y : TateModule p (G'.Points (PadicAlgCl p)), ∑ j, κ p R (c j) * dα j y = 0) :
    c = 0 := by
  classical
  funext j₀

  let τ : G.tangentSpace R := ∑ j, c j • b.coord j

  have hτ : ∀ (y : TateModule p (G'.Points (PadicAlgCl p))) (v : ℕ) (ψ : G'.Point (OR p R) v),
      G'.pointsMkAdd (PadicAlgCl p) v (Additive.ofMul (G'.pointMap (OR p R).val v ψ)) =
        (y : ℕ → G'.Points (PadicAlgCl p)) v →
      ∀ z : OR p R ⊗[R] G.cotangentModule, projS p G v z = D.charDiff (OR p R) v ψ →
        evalS p G τ z ∈ Ideal.span {(p : OR p R) ^ v} := by
    intro y v ψ hψ z hz
    exact evalS_mem_span p G hval hR1 b c (fun j => dα j y) z v (hc y) fun j => hdα j y v ψ hψ z hz

  obtain ⟨m, cc, e, hcc, he, hpair⟩ :=
    PDivisibleGroup.CartierDuality.exists_addMonoidHom_tangentSpace_cpoints_pair_eq_sum_pow_of_ker_cotangentModuleProj_eq
      p htf hsep D hsurj hker
  have hcc0 : cc 0 = 1 := by
    have := hcc 0
    rwa [Nat.factorial_zero, Nat.cast_one, one_mul, mul_zero, pow_zero] at this

  have hg0 : e τ = 0 := by
    refine hstep4 (e τ) ?_
    intro y i w hiw f hf ψ hψ

    obtain ⟨z, hz⟩ := LinearMap.lTensor_surjective (OR p R) (hsurj w) (D.charDiff (OR p R) w ψ)

    have hmk : Ideal.Quotient.mk (Ideal.span {(p : OR p R) ^ i})
        (TensorProduct.rid R (OR p R) (τ.lTensor (OR p R) z)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (span_pow_mono p hiw (hτ y w ψ hψ z hz))
    rw [hpair (OR p R) τ i w hiw f hf ψ z hz, hmk]
    rcases Nat.eq_zero_or_pos i with hi | hi
    ·
      subst hi
      haveI : Subsingleton (OR p R ⧸ Ideal.span {(p : OR p R) ^ 0}) :=
        Ideal.Quotient.subsingleton_iff.mpr (by rw [pow_zero, Ideal.span_singleton_one])
      exact Subsingleton.elim _ _
    · exact sum_range_mul_zero_pow (algebraMap R _) i hi.ne' cc hcc0

  have hτ0 : τ = 0 := he (by rw [hg0, map_zero])
  have h1 : τ (b j₀) = c j₀ := by
    simp only [τ, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, Module.Basis.coord_apply,
      Module.Basis.repr_self, smul_eq_mul]
    rw [Finset.sum_eq_single j₀]
    · simp
    · intro j _ hj
      rw [Finsupp.single_eq_of_ne hj, mul_zero]
    · intro hj₀; exact absurd (Finset.mem_univ _) hj₀
  rw [Pi.zero_apply, ← h1, hτ0, LinearMap.zero_apply]

end Generic

section Base

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

noncomputable abbrev OK : Type := PadicAlgCl.ringOfIntegers p K

theorem hval_K (x : PadicAlgCl p) (hx : ‖x‖ ≤ 1) : x ∈ OR p (OK p K) :=
  ((PadicAlgCl.isIntegral_padicInt_iff_norm_le_one p x).mpr hx).tower_top

theorem hR1_K (a : OK p K) : ‖algebraMap (OK p K) (PadicAlgCl p) a‖ ≤ 1 :=
  PadicAlgCl.ringOfIntegers.norm_coe_le_one p K a

theorem htf_K (x : OK p K) (hx : ((p : ℕ) : OK p K) * x = 0) : x = 0 := by
  have hp0 : (p : PadicAlgCl p) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have h1 : ((((p : ℕ) : OK p K) * x : OK p K) : PadicAlgCl p) = 0 := by rw [hx]; rfl
  rw [Subalgebra.coe_mul] at h1
  have h2 : (((p : ℕ) : OK p K) : PadicAlgCl p) = (p : PadicAlgCl p) := rfl
  rw [h2] at h1
  exact Subtype.ext ((mul_eq_zero.mp h1).resolve_left hp0)

theorem hsep_K (x : OK p K) (hx : ∀ i : ℕ, x ∈ Ideal.span {((p : ℕ) : OK p K) ^ i}) : x = 0 := by

  have hnorm : ∀ i : ℕ, ‖(x : PadicAlgCl p)‖ ≤ ((p : ℝ)⁻¹) ^ i := by
    intro i
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp (hx i)
    have hcoe : (x : PadicAlgCl p) = (d : PadicAlgCl p) * (p : PadicAlgCl p) ^ i := by
      rw [← hd, Subalgebra.coe_mul, SubmonoidClass.coe_pow]; rfl
    rw [hcoe, norm_mul, norm_pow, norm_coe_p]
    calc ‖(d : PadicAlgCl p)‖ * (p : ℝ)⁻¹ ^ i ≤ 1 * (p : ℝ)⁻¹ ^ i :=
          mul_le_mul_of_nonneg_right (PadicAlgCl.ringOfIntegers.norm_coe_le_one p K d) (by positivity)
      _ = _ := one_mul _
  by_contra hne
  have hne' : (x : PadicAlgCl p) ≠ 0 := fun h0 => hne (Subtype.ext h0)
  have hpos : 0 < ‖(x : PadicAlgCl p)‖ := norm_pos_iff.mpr hne'
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hpos (inv_lt_one_of_one_lt₀ hp1)
  exact absurd (hnorm m) (not_le.mpr hm)

theorem hR_K (x : PadicAlgCl p) :
    x ∈ Set.range (algebraMap (OK p K) (PadicAlgCl p)) ↔ x ∈ K ∧ ‖x‖ ≤ 1 := by
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨PadicAlgCl.ringOfIntegers.coe_mem r, PadicAlgCl.ringOfIntegers.norm_coe_le_one p K r⟩
  · rintro ⟨hK, hn⟩
    exact ⟨⟨x, (PadicAlgCl.isIntegral_padicInt_iff_norm_le_one p x).mpr hn, hK⟩, rfl⟩

theorem hinj_K : Function.Injective (algebraMap (OK p K) (PadicAlgCl p)) := Subtype.val_injective

theorem smul_eq_coe_mul (k : K) (c : ℂ_[p]) : k • c = ((k : PadicAlgCl p) : ℂ_[p]) * c :=
  Algebra.smul_def (k : PadicAlgCl p) c

theorem exists_pow_mul_eq {n : ℕ} (q : Fin n → K) :
    ∃ (N : ℕ) (c : Fin n → OK p K), ∀ j, (c j : PadicAlgCl p) = (p : PadicAlgCl p) ^ N * (q j : PadicAlgCl p) := by
  classical
  have hex : ∀ j, ∃ (m : ℕ) (y : OK p K), (y : PadicAlgCl p) = (p : PadicAlgCl p) ^ m * (q j : PadicAlgCl p) :=
    fun j => PadicAlgCl.ringOfIntegers.exists_pow_natCast_mul_mem p K (q j).2
  choose m y hy using hex
  refine ⟨∑ j, m j, fun j => ⟨(p : PadicAlgCl p) ^ (∑ j', m j' - m j), Subalgebra.pow_mem _
    (PadicAlgCl.ringOfIntegers.natCast_mem p K p) _⟩ * y j, fun j => ?_⟩
  have hle : m j ≤ ∑ j', m j' := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  rw [Subalgebra.coe_mul, hy j, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

variable [FiniteDimensional ℚ_[p] K]

theorem tower_K {h : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h) {n : ℕ}
    (hn : G.HasDimension n) : Tower p G := by
  obtain ⟨-, hdvr, hcomplete⟩ :=
    PadicAlgCl.ringOfIntegers.finite_and_isDiscreteValuationRing_and_isAdicComplete p K
  haveI := hdvr
  haveI := hcomplete
  have hp : ((p : ℕ) : PadicAlgCl.ringOfIntegers p K) ∈
      IsLocalRing.maximalIdeal (PadicAlgCl.ringOfIntegers p K) :=
    (IsLocalRing.mem_maximalIdeal _).2 (PadicAlgCl.ringOfIntegers.not_isUnit_natCast p K)
  have hlim := PDivisibleGroup.nonempty_basis_cotangentModule_of_hasDimension
    (IsLocalRing.maximalIdeal (PadicAlgCl.ringOfIntegers p K)) hp G hn
  exact ⟨hlim.2.1, hlim.2.2⟩

end Base

end PDivINJK

open PDivINJK in

theorem solution
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} {G G' : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h} (D : G.CartierDuality G')
    {n : ℕ} (hn : G.HasDimension n)
    (b : Module.Basis (Fin n) (PadicAlgCl.ringOfIntegers p K) G.cotangentModule)
    (dα : Fin n → (TateModule p (G'.Points (PadicAlgCl p)) →+ ℂ_[p]))
    (hdα : ∀ (j : Fin n) (y : TateModule p (G'.Points (PadicAlgCl p))) (v : ℕ)
        (ψ : G'.Point (integralClosure (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p)) v),
        G'.pointsMkAdd (PadicAlgCl p) v
            (Additive.ofMul (G'.pointMap
              (integralClosure (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p)).val v ψ)) =
          (y : ℕ → G'.Points (PadicAlgCl p)) v →
        ∀ z : integralClosure (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p)
            ⊗[PadicAlgCl.ringOfIntegers p K] G.cotangentModule,
          (G.cotangentModuleProj v).lTensor
              (integralClosure (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p)) z =
            D.charDiff (integralClosure (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p)) v ψ →
          ‖dα j y - ((TensorProduct.rid (PadicAlgCl.ringOfIntegers p K)
              (integralClosure (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p))
              ((b.coord j).lTensor
                (integralClosure (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p)) z) :
                PadicAlgCl p) : ℂ_[p])‖ ≤
            (p : ℝ) ^ (-(v : ℤ))) :
    LinearIndependent K
      (fun j => (⇑(dα j) : TateModule p (G'.Points (PadicAlgCl p)) → ℂ_[p])) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro q hq j₀

  have hqy : ∀ y : TateModule p (G'.Points (PadicAlgCl p)), ∑ j, q j • dα j y = 0 := by
    intro y
    have := congr_fun hq y
    simpa only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] using this

  obtain ⟨N, c, hc⟩ := exists_pow_mul_eq p K q
  have hcy : ∀ y : TateModule p (G'.Points (PadicAlgCl p)),
      ∑ j, κ p (OK p K) (c j) * dα j y = 0 := by
    intro y
    have h1 : ∀ j, κ p (OK p K) (c j) * dα j y =
        (((p : PadicAlgCl p) ^ N : PadicAlgCl p) : ℂ_[p]) * (q j • dα j y) := by
      intro j
      have h2 : κ p (OK p K) (c j) =
          (((p : PadicAlgCl p) ^ N : PadicAlgCl p) : ℂ_[p]) * ((q j : PadicAlgCl p) : ℂ_[p]) := by
        change (((c j : PadicAlgCl p)) : ℂ_[p]) = _
        rw [hc j, UniformSpace.Completion.coe_mul]
      rw [h2, smul_eq_coe_mul, mul_assoc]
    simp_rw [h1]
    rw [← Finset.mul_sum, hqy y, mul_zero]

  have hT := tower_K p K G hn
  have h0 : c = 0 :=
    eq_zero_of_forall_sum_eq_zero p (hval_K p K) (hR1_K p K) (htf_K p K) (hsep_K p K) D hT.surj hT.ker
      (fun g hg =>
        PDivisibleGroup.CartierDuality.cpoints_eq_zero_of_forall_pair_eq_one_of_forall_mem_range_iff
          p K (hR_K p K) (hinj_K p K) D g hg)
      b dα hdα c hcy

  have hp0 : (p : PadicAlgCl p) ^ N ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have h1 : (p : PadicAlgCl p) ^ N * (q j₀ : PadicAlgCl p) = 0 := by
    rw [← hc j₀, h0]; rfl
  have h2 : (q j₀ : PadicAlgCl p) = 0 := (mul_eq_zero.mp h1).resolve_left hp0
  exact_mod_cast h2

end S_PDivisibleGroup_CartierDuality_linearIndependent_tateModule_padicComplex_of_norm_sub_le_of_ringOfIntegers
end P2MW
export P2MW.S_PDivisibleGroup_CartierDuality_linearIndependent_tateModule_padicComplex_of_norm_sub_le_of_ringOfIntegers (solution)
