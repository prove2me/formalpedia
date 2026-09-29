-- Prove2me | solution 1 for PDivisibleGroup.CartierDuality.exists_addMonoidHom_tateModule_padicComplex_smul_eq_and_norm_sub_le_of_ringOfIntegers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/255c796c-188e-5a8d-a761-be98f991e106

import Mathlib
import Definitions.Def_PadicComplex_GaloisAction
import Definitions.Def_PDivisibleGroup_CharacterDifferential
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Theorems.Thm_PDivisibleGroup_nonempty_basis_cotangentModule_of_hasDimension
import Theorems.Thm_PDivisibleGroup_CartierDuality_exists_addMonoidHom_tateModule_apply_eq_charDiff
import Theorems.Thm_PDivisibleGroup_bijective_pointsMap_val_integralClosure_and_exists_tateModule_equiv
import Theorems.Thm_PadicAlgCl_ringOfIntegers_finite_and_isDiscreteValuationRing_and_isAdicComplete
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_CartierDuality_exists_addMonoidHom_tateModule_padicComplex_smul_eq_and_norm_sub_le_of_ringOfIntegers

set_option autoImplicit false

open PDivisibleGroup Filter Topology
open scoped TensorProduct

namespace PDivDAlphaK

variable (p : ℕ) [Fact p.Prime]

section Limits

variable {O : Type} [CommRing O] (ι : O →+* ℂ_[p]) (hι : ∀ c : O, ‖ι c‖ ≤ 1)

theorem norm_sub_le_max (a b : ℂ_[p]) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  simpa [sub_eq_add_neg, norm_neg] using PadicComplex.isNonarchimedean p a (-b)

theorem norm_add_le_max (a b : ℂ_[p]) : ‖a + b‖ ≤ max ‖a‖ ‖b‖ := PadicComplex.isNonarchimedean p a b

theorem norm_ι_p_pow (v : ℕ) : ‖ι ((p : O) ^ v)‖ = (p : ℝ) ^ (-(v : ℤ)) := by
  rw [map_pow, map_natCast, norm_pow]
  have h1 : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]) p]
    exact (PadicComplex.norm_extends' (p := p) (p : ℚ_[p])).trans (Padic.norm_p (p := p))
  rw [h1, zpow_neg, zpow_natCast, inv_pow]

include hι in

theorem norm_ι_le_of_mem_span (v : ℕ) {c : O} (hc : c ∈ Ideal.span {(p : O) ^ v}) :
    ‖ι c‖ ≤ (p : ℝ) ^ (-(v : ℤ)) := by
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hc
  rw [map_mul, norm_mul, norm_ι_p_pow]
  calc ‖ι d‖ * (p : ℝ) ^ (-(v : ℤ)) ≤ 1 * (p : ℝ) ^ (-(v : ℤ)) :=
        mul_le_mul_of_nonneg_right (hι d) (by positivity)
    _ = (p : ℝ) ^ (-(v : ℤ)) := one_mul _

def IsLim (c : ℕ → O) (ℓ : ℂ_[p]) : Prop := ∀ v, ‖ℓ - ι (c v)‖ ≤ (p : ℝ) ^ (-(v : ℤ))

def IsCauchy (c : ℕ → O) : Prop := ∀ v, c (v + 1) - c v ∈ Ideal.span {(p : O) ^ v}

theorem pow_antitone {v w : ℕ} (hvw : v ≤ w) : (p : ℝ) ^ (-(w : ℤ)) ≤ (p : ℝ) ^ (-(v : ℤ)) := by
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  exact zpow_le_zpow_right₀ hp (neg_le_neg (Int.ofNat_le.mpr hvw))

include hι in
theorem IsCauchy.norm_sub_le {c : ℕ → O} (hc : IsCauchy p c) {v w : ℕ} (hvw : v ≤ w) :
    ‖ι (c w) - ι (c v)‖ ≤ (p : ℝ) ^ (-(v : ℤ)) := by
  induction w, hvw using Nat.le_induction with
  | base => simp
  | succ w hvw ih =>
      have h1 : ‖ι (c (w + 1)) - ι (c w)‖ ≤ (p : ℝ) ^ (-(v : ℤ)) := by
        rw [← map_sub]
        exact (norm_ι_le_of_mem_span p ι hι w (hc w)).trans (pow_antitone p hvw)
      calc ‖ι (c (w + 1)) - ι (c v)‖
          = ‖(ι (c (w + 1)) - ι (c w)) + (ι (c w) - ι (c v))‖ := by rw [sub_add_sub_cancel]
        _ ≤ max ‖ι (c (w + 1)) - ι (c w)‖ ‖ι (c w) - ι (c v)‖ := norm_add_le_max p _ _
        _ ≤ (p : ℝ) ^ (-(v : ℤ)) := max_le h1 ih

include hι in

theorem IsCauchy.exists_isLim {c : ℕ → O} (hc : IsCauchy p c) : ∃ ℓ, IsLim p ι c ℓ := by
  have hp1 : (p : ℝ)⁻¹ < 1 := by
    have : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    exact inv_lt_one_of_one_lt₀ this
  have hcs : CauchySeq fun v => ι (c v) := by
    refine cauchySeq_of_le_geometric ((p : ℝ)⁻¹) 1 hp1 fun v => ?_
    rw [dist_comm, dist_eq_norm, one_mul, inv_pow, ← zpow_natCast, ← zpow_neg, ← map_sub]
    exact norm_ι_le_of_mem_span p ι hι v (hc v)
  obtain ⟨ℓ, hℓ⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨ℓ, fun v => ?_⟩
  have ht : Tendsto (fun w => ‖ι (c w) - ι (c v)‖) atTop (𝓝 ‖ℓ - ι (c v)‖) :=
    (hℓ.sub_const _).norm
  exact le_of_tendsto ht (Filter.eventually_atTop.mpr ⟨v, fun w hw => hc.norm_sub_le p ι hι hw⟩)

include hι in

theorem IsLim.eq_of_forall_sub_mem {c c' : ℕ → O} {ℓ ℓ' : ℂ_[p]} (h : IsLim p ι c ℓ)
    (h' : IsLim p ι c' ℓ') (hcc' : ∀ v, c v - c' v ∈ Ideal.span {(p : O) ^ v}) : ℓ = ℓ' := by
  rw [← sub_eq_zero, ← norm_le_zero_iff]

  have hle : ∀ v : ℕ, ‖ℓ - ℓ'‖ ≤ (p : ℝ) ^ (-(v : ℤ)) := by
    intro v
    have h1 : ℓ - ℓ' = (ℓ - ι (c v)) + (ι (c v - c' v)) - (ℓ' - ι (c' v)) := by
      rw [map_sub]; abel
    rw [h1]
    refine (norm_sub_le_max p _ _).trans (max_le ?_ (h' v))
    refine (norm_add_le_max p _ _).trans (max_le (h v) ?_)
    exact norm_ι_le_of_mem_span p ι hι v (hcc' v)

  have ht : Tendsto (fun v : ℕ => (p : ℝ) ^ (-(v : ℤ))) atTop (𝓝 0) := by
    have : (fun v : ℕ => (p : ℝ) ^ (-(v : ℤ))) = fun v : ℕ => ((p : ℝ)⁻¹) ^ v := by
      funext v; rw [zpow_neg, zpow_natCast, inv_pow]
    rw [this]
    refine tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ?_
    have : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    exact inv_lt_one_of_one_lt₀ this
  exact ge_of_tendsto' ht hle

theorem IsLim.add {c c' : ℕ → O} {ℓ ℓ' : ℂ_[p]} (h : IsLim p ι c ℓ) (h' : IsLim p ι c' ℓ') :
    IsLim p ι (c + c') (ℓ + ℓ') := by
  intro v
  have h1 : ℓ + ℓ' - ι ((c + c') v) = (ℓ - ι (c v)) + (ℓ' - ι (c' v)) := by
    rw [Pi.add_apply, map_add]; abel
  rw [h1]
  exact (norm_add_le_max p _ _).trans (max_le (h v) (h' v))

include hι in

theorem IsLim.smul {c : ℕ → O} {ℓ : ℂ_[p]} (h : IsLim p ι c ℓ) (a : ℤ_[p]) :
    IsLim p ι (fun v => (a.appr v : O) * c v) ((a : ℚ_[p]) • ℓ) := by
  intro v

  have hcast : ι ((a.appr v : O) * c v) = ((a.appr v : ℚ_[p]) : ℚ_[p]) • ι (c v) := by
    rw [map_mul, map_natCast, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
  have h1 : (a : ℚ_[p]) • ℓ - ι ((a.appr v : O) * c v) =
      (a : ℚ_[p]) • (ℓ - ι (c v)) + ((a : ℚ_[p]) - (a.appr v : ℚ_[p])) • ι (c v) := by
    rw [hcast, smul_sub, sub_smul]; abel
  rw [h1]
  refine (norm_add_le_max p _ _).trans (max_le ?_ ?_)
  · rw [norm_smul]
    calc ‖(a : ℚ_[p])‖ * ‖ℓ - ι (c v)‖ ≤ 1 * (p : ℝ) ^ (-(v : ℤ)) :=
          mul_le_mul (PadicInt.norm_le_one a) (h v) (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  · rw [norm_smul]
    have happr : ‖(a : ℚ_[p]) - (a.appr v : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(v : ℤ)) := by
      have hmem := PadicInt.appr_spec v a
      rw [← PadicInt.norm_le_pow_iff_mem_span_pow] at hmem
      rw [show (a : ℚ_[p]) - (a.appr v : ℚ_[p]) = ((a - a.appr v : ℤ_[p]) : ℚ_[p]) by push_cast; ring]
      rw [PadicInt.padic_norm_e_of_padicInt]
      exact hmem
    calc ‖(a : ℚ_[p]) - (a.appr v : ℚ_[p])‖ * ‖ι (c v)‖ ≤ (p : ℝ) ^ (-(v : ℤ)) * 1 :=
          mul_le_mul happr (hι _) (norm_nonneg _) (by positivity)
      _ = _ := mul_one _

theorem IsLim.gal {c : ℕ → O} {ℓ : ℂ_[p]} (h : IsLim p ι c ℓ) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (σ' : O → O) (hσ : ∀ x : O, ι (σ' x) = σ • ι x) :
    IsLim p ι (fun v => σ' (c v)) (σ • ℓ) := by
  intro v
  rw [hσ, ← smul_sub, PadicComplex.norm_smul_eq]
  exact h v

end Limits

theorem exact_lTensor_ker_subtype {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (g : M →ₗ[R] N) (Q : Type) [AddCommGroup Q] [Module R Q]
    (hs : Function.Surjective g) :
    Function.Exact ((LinearMap.ker g).subtype.lTensor Q) (g.lTensor Q) :=
  lTensor_exact Q (LinearMap.exact_subtype_ker_map g) hs

section Coord

variable {R : Type} [CommRing R] (O : Type) [CommRing O] [Algebra R O]
variable {h : ℕ} (G : PDivisibleGroup R p h) {n : ℕ}

noncomputable abbrev projS (v : ℕ) :
    O ⊗[R] G.cotangentModule →ₗ[R] O ⊗[R] G.Cotangent v :=
  (G.cotangentModuleProj v).lTensor O

noncomputable abbrev coordS (b : Module.Basis (Fin n) R G.cotangentModule) (j : Fin n) :
    O ⊗[R] G.cotangentModule →ₗ[R] O :=
  (TensorProduct.rid R O).toLinearMap ∘ₗ (b.coord j).lTensor O

omit [Fact p.Prime] in
theorem coordS_tmul (b : Module.Basis (Fin n) R G.cotangentModule) (j : Fin n) (s : O)
    (w : G.cotangentModule) : coordS p O G b j (s ⊗ₜ[R] w) = b.coord j w • s := by
  simp [coordS]

omit [Fact p.Prime] in

theorem lTensor_cotangentMap_projS (v : ℕ) (z : O ⊗[R] G.cotangentModule) :
    (G.cotangentMap v).lTensor O (projS p O G (v + 1) z) = projS p O G v z := by
  have hc : (G.cotangentMap v) ∘ₗ (G.cotangentModuleProj (v + 1)) = G.cotangentModuleProj v :=
    LinearMap.ext fun w => G.cotangentMap_cotangentModuleProj v w
  change (G.cotangentMap v).lTensor O ((G.cotangentModuleProj (v + 1)).lTensor O z) =
    (G.cotangentModuleProj v).lTensor O z
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hc]

omit [Fact p.Prime] in

theorem projS_map (v : ℕ) (τ : O →ₗ[R] O) (z : O ⊗[R] G.cotangentModule) :
    projS p O G v (TensorProduct.map τ LinearMap.id z) =
      TensorProduct.map τ LinearMap.id (projS p O G v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s w => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, ← map_add, ← map_add]

omit [Fact p.Prime] in

theorem coordS_map (b : Module.Basis (Fin n) R G.cotangentModule) (j : Fin n) (τ : O →ₗ[R] O)
    (z : O ⊗[R] G.cotangentModule) :
    coordS p O G b j (TensorProduct.map τ LinearMap.id z) = τ (coordS p O G b j z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s w =>
      rw [TensorProduct.map_tmul, LinearMap.id_apply, coordS_tmul, coordS_tmul, map_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

structure Tower : Prop where
  surj : ∀ v, Function.Surjective (G.cotangentModuleProj v)
  ker : ∀ v, LinearMap.ker (G.cotangentModuleProj v) = Ideal.span {(p : R) ^ v} • ⊤

variable {G} (hT : Tower p G)
include hT

omit [Fact p.Prime] in
theorem projS_surjective (v : ℕ) : Function.Surjective (projS p O G v) :=
  LinearMap.lTensor_surjective O (hT.surj v)

omit [Fact p.Prime] in

theorem coordS_mem_of_projS_eq_zero (b : Module.Basis (Fin n) R G.cotangentModule) (j : Fin n)
    (v : ℕ) (z : O ⊗[R] G.cotangentModule) (hz : projS p O G v z = 0) :
    coordS p O G b j z ∈ Ideal.span {(p : O) ^ v} := by
  have hex := exact_lTensor_ker_subtype (G.cotangentModuleProj v) O (hT.surj v)
  obtain ⟨t, rfl⟩ := (hex z).mp hz
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; exact Ideal.zero_mem _
  | tmul s w =>
      rw [LinearMap.lTensor_tmul, Submodule.subtype_apply, coordS_tmul]
      have hw : (w : G.cotangentModule) ∈ Ideal.span {(p : R) ^ v} • (⊤ : Submodule R G.cotangentModule) := by
        rw [← hT.ker v]; exact w.2
      rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hw
      obtain ⟨w', -, hw'⟩ := hw
      rw [← hw', map_smul, smul_eq_mul, mul_smul, Algebra.smul_def, map_pow, map_natCast]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  | add x y hx hy =>
      rw [map_add, map_add] at hz ⊢
      have hx' : projS p O G v ((LinearMap.lTensor O (LinearMap.ker (G.cotangentModuleProj v)).subtype) x) = 0 :=
        (hex _).mpr ⟨x, rfl⟩
      have hy' : projS p O G v ((LinearMap.lTensor O (LinearMap.ker (G.cotangentModuleProj v)).subtype) y) = 0 :=
        (hex _).mpr ⟨y, rfl⟩
      exact Ideal.add_mem _ (hx hx') (hy hy')

omit [Fact p.Prime] in
theorem coordS_sub_mem (b : Module.Basis (Fin n) R G.cotangentModule) (j : Fin n) (v : ℕ)
    {z z' : O ⊗[R] G.cotangentModule} (hzz' : projS p O G v z = projS p O G v z') :
    coordS p O G b j z - coordS p O G b j z' ∈ Ideal.span {(p : O) ^ v} := by
  rw [← map_sub]
  exact coordS_mem_of_projS_eq_zero p O hT b j v _ (by rw [map_sub, hzz', sub_self])

end Coord

section Family

variable {R : Type} [CommRing R] {O : Type} [CommRing O] [Algebra R O]
  (ι : O →+* ℂ_[p]) (hι : ∀ c : O, ‖ι c‖ ≤ 1)
  {h : ℕ} {G : PDivisibleGroup R p h} (G' : PDivisibleGroup R p h) {n : ℕ} (hT : Tower p G)
  (b : Module.Basis (Fin n) R G.cotangentModule)
  (HT : TateModule p (G'.Points O) →+ ((v : ℕ) → O ⊗[R] G.Cotangent v))
  (hcompat : ∀ (x : TateModule p (G'.Points O)) (v : ℕ),
    (G.cotangentMap v).lTensor O (HT x (v + 1)) = HT x v)
include hT

noncomputable def zed (x : TateModule p (G'.Points O)) (v : ℕ) : O ⊗[R] G.cotangentModule :=
  (projS_surjective p O hT v (HT x v)).choose

omit [Fact p.Prime] in
theorem projS_zed (x : TateModule p (G'.Points O)) (v : ℕ) :
    projS p O G v (zed p G' hT HT x v) = HT x v :=
  (projS_surjective p O hT v (HT x v)).choose_spec

noncomputable def cseq (j : Fin n) (x : TateModule p (G'.Points O)) : ℕ → O :=
  fun v => coordS p O G b j (zed p G' hT HT x v)

omit [Fact p.Prime] in
include hcompat in
theorem cseq_isCauchy (j : Fin n) (x : TateModule p (G'.Points O)) : IsCauchy p (cseq p G' hT b HT j x) := by
  intro v
  refine coordS_sub_mem p O hT b j v ?_
  rw [← lTensor_cotangentMap_projS, projS_zed, projS_zed, hcompat]

include hι

noncomputable def ell (j : Fin n) (x : TateModule p (G'.Points O)) : ℂ_[p] :=
  (IsCauchy.exists_isLim p ι hι (cseq_isCauchy p G' hT b HT hcompat j x)).choose

theorem ell_spec (j : Fin n) (x : TateModule p (G'.Points O)) :
    IsLim p ι (cseq p G' hT b HT j x) (ell p ι hι G' hT b HT hcompat j x) :=
  (IsCauchy.exists_isLim p ι hι (cseq_isCauchy p G' hT b HT hcompat j x)).choose_spec

theorem norm_ell_sub_le (j : Fin n) (x : TateModule p (G'.Points O)) (v : ℕ)
    (z : O ⊗[R] G.cotangentModule) (hz : projS p O G v z = HT x v) :
    ‖ell p ι hι G' hT b HT hcompat j x - ι (coordS p O G b j z)‖ ≤ (p : ℝ) ^ (-(v : ℤ)) := by
  have h1 : ell p ι hι G' hT b HT hcompat j x - ι (coordS p O G b j z) =
      (ell p ι hι G' hT b HT hcompat j x - ι (cseq p G' hT b HT j x v)) +
        ι (cseq p G' hT b HT j x v - coordS p O G b j z) := by
    rw [map_sub]; abel
  rw [h1]
  refine (norm_add_le_max p _ _).trans (max_le (ell_spec p ι hι G' hT b HT hcompat j x v) ?_)
  exact norm_ι_le_of_mem_span p ι hι v (coordS_sub_mem p O hT b j v (by rw [projS_zed, hz]))

theorem ell_add (j : Fin n) (x y : TateModule p (G'.Points O)) :
    ell p ι hι G' hT b HT hcompat j (x + y) =
      ell p ι hι G' hT b HT hcompat j x + ell p ι hι G' hT b HT hcompat j y := by
  refine IsLim.eq_of_forall_sub_mem p ι hι (ell_spec p ι hι G' hT b HT hcompat j (x + y))
    ((ell_spec p ι hι G' hT b HT hcompat j x).add p ι (ell_spec p ι hι G' hT b HT hcompat j y)) fun v => ?_
  dsimp only [cseq, Pi.add_apply]
  rw [← map_add]
  exact coordS_sub_mem p O hT b j v (by rw [map_add, projS_zed, projS_zed, projS_zed, map_add, Pi.add_apply])

theorem ell_smul (hsmul : ∀ (a : ℤ_[p]) (x : TateModule p (G'.Points O)) (v : ℕ),
      HT (a • x) v = a.appr v • HT x v)
    (j : Fin n) (a : ℤ_[p]) (x : TateModule p (G'.Points O)) :
    ell p ι hι G' hT b HT hcompat j (a • x) = (a : ℚ_[p]) • ell p ι hι G' hT b HT hcompat j x := by
  refine IsLim.eq_of_forall_sub_mem p ι hι (ell_spec p ι hι G' hT b HT hcompat j (a • x))
    ((ell_spec p ι hι G' hT b HT hcompat j x).smul p ι hι a) fun v => ?_
  dsimp only [cseq]
  rw [← nsmul_eq_mul, ← map_nsmul]
  exact coordS_sub_mem p O hT b j v (by rw [map_nsmul, projS_zed, projS_zed, hsmul])

theorem ell_rep (σ' : O ≃ₐ[R] O)
    (hrep : ∀ (x : TateModule p (G'.Points O)) (v : ℕ),
      HT (G'.tateModuleRep O σ' x) v =
        TensorProduct.map (AlgEquiv.toAlgHom σ').toLinearMap LinearMap.id (HT x v))
    (j : Fin n) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hσ : ∀ x : O, ι (σ' x) = σ • ι x) (x : TateModule p (G'.Points O)) :
    ell p ι hι G' hT b HT hcompat j (G'.tateModuleRep O σ' x) = σ • ell p ι hι G' hT b HT hcompat j x := by
  refine IsLim.eq_of_forall_sub_mem p ι hι (ell_spec p ι hι G' hT b HT hcompat j _)
    ((ell_spec p ι hι G' hT b HT hcompat j x).gal p ι σ σ' hσ) fun v => ?_
  dsimp only [cseq]
  have h1 : σ' (coordS p O G b j (zed p G' hT HT x v)) = coordS p O G b j
      (TensorProduct.map (AlgEquiv.toAlgHom σ').toLinearMap LinearMap.id (zed p G' hT HT x v)) :=
    (coordS_map p O G b j (AlgEquiv.toAlgHom σ').toLinearMap (zed p G' hT HT x v)).symm
  rw [h1]
  refine coordS_sub_mem p O hT b j v ?_
  rw [projS_zed, hrep, projS_map, projS_zed]

end Family

section Generic

variable {R : Type} [CommRing R] [Algebra R (PadicAlgCl p)]

noncomputable abbrev OR (R : Type) [CommRing R] [Algebra R (PadicAlgCl p)] : Subalgebra R (PadicAlgCl p) :=
  integralClosure R (PadicAlgCl p)

noncomputable def ιR (R : Type) [CommRing R] [Algebra R (PadicAlgCl p)] : OR p R →+* ℂ_[p] :=
  (algebraMap (PadicAlgCl p) ℂ_[p]).comp (OR p R).val.toRingHom

theorem ιR_apply (c : OR p R) : ιR p R c = ((c : PadicAlgCl p) : ℂ_[p]) := rfl

theorem ιR_restrict (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (τ : PadicAlgCl p ≃ₐ[R] PadicAlgCl p) (hτσ : ∀ x : PadicAlgCl p, τ x = σ x)
    (τ' : OR p R ≃ₐ[R] OR p R)
    (hτ' : ∀ x : OR p R, ((τ' x : OR p R) : PadicAlgCl p) = τ x) (x : OR p R) :
    ιR p R (τ' x) = σ • ιR p R x := by
  rw [ιR_apply, ιR_apply, hτ', hτσ, ← PadicComplex.smul_coe]

theorem exists_dα (hO : ∀ c : OR p R, ‖ιR p R c‖ ≤ 1)
    {h : ℕ} {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G') {n : ℕ} (hT : Tower p G)
    (b : Module.Basis (Fin n) R G.cotangentModule) :
    ∃ dα : Fin n → (TateModule p (G'.Points (PadicAlgCl p)) →+ ℂ_[p]),
      (∀ (j : Fin n) (a : ℤ_[p]) (y : TateModule p (G'.Points (PadicAlgCl p))),
          dα j (a • y) = (a : ℚ_[p]) • dα j y) ∧
      (∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (τ : PadicAlgCl p ≃ₐ[R] PadicAlgCl p),
          (∀ x : PadicAlgCl p, τ x = σ x) →
          ∀ (j : Fin n) (y : TateModule p (G'.Points (PadicAlgCl p))),
          dα j (G'.tateModuleRep (PadicAlgCl p) τ y) = σ • dα j y) ∧
      (∀ (j : Fin n) (y : TateModule p (G'.Points (PadicAlgCl p))) (v : ℕ) (ψ : G'.Point (OR p R) v),
          G'.pointsMkAdd (PadicAlgCl p) v (Additive.ofMul (G'.pointMap (OR p R).val v ψ)) =
            (y : ℕ → G'.Points (PadicAlgCl p)) v →
          ∀ z : OR p R ⊗[R] G.cotangentModule,
            (G.cotangentModuleProj v).lTensor (OR p R) z = D.charDiff (OR p R) v ψ →
            ‖dα j y - ((TensorProduct.rid R (OR p R) ((b.coord j).lTensor (OR p R) z) : PadicAlgCl p) : ℂ_[p])‖ ≤
              (p : ℝ) ^ (-(v : ℤ))) := by

  obtain ⟨HT, hlvl, hcompat, hsmul, hrep⟩ :=
    PDivisibleGroup.CartierDuality.exists_addMonoidHom_tateModule_apply_eq_charDiff D (OR p R)

  obtain ⟨hbij, hrestr, -, e, he, herep⟩ :=
    PDivisibleGroup.bijective_pointsMap_val_integralClosure_and_exists_tateModule_equiv G' (PadicAlgCl p)

  let ℓ : Fin n → TateModule p (G'.Points (OR p R)) → ℂ_[p] := fun j =>
    ell p (ιR p R) hO G' hT b HT hcompat j
  have hℓ_add : ∀ j x x', ℓ j (x + x') = ℓ j x + ℓ j x' := fun j =>
    ell_add p (ιR p R) hO G' hT b HT hcompat j

  let dα : Fin n → (TateModule p (G'.Points (PadicAlgCl p)) →+ ℂ_[p]) := fun j =>
    AddMonoidHom.mk' (fun y => ℓ j (e.symm y)) fun y y' => by
      change ℓ j (e.symm (y + y')) = ℓ j (e.symm y) + ℓ j (e.symm y')
      rw [map_add, hℓ_add]
  have hdα : ∀ j y, dα j y = ℓ j (e.symm y) := fun _ _ => rfl
  refine ⟨dα, ?_, ?_, ?_⟩
  · intro j a y
    rw [hdα, hdα, LinearEquiv.map_smul]
    exact ell_smul p (ιR p R) hO G' hT b HT hcompat hsmul j a _
  · intro σ τ hτσ j y
    obtain ⟨τ', hτ'⟩ := hrestr τ
    have hy : e.symm (G'.tateModuleRep (PadicAlgCl p) τ y) = G'.tateModuleRep (OR p R) τ' (e.symm y) := by
      rw [LinearEquiv.symm_apply_eq, herep _ τ' hτ', LinearEquiv.apply_symm_apply]
    rw [hdα, hdα, hy]
    exact ell_rep p (ιR p R) hO G' hT b HT hcompat τ' (hrep τ') j σ (ιR_restrict p σ τ hτσ τ' hτ') _
  · intro j y v ψ hψ z hz
    rw [hdα]
    change ‖ℓ j (e.symm y) - ιR p R (coordS p (OR p R) G b j z)‖ ≤ _
    refine norm_ell_sub_le p (ιR p R) hO G' hT b HT hcompat j (e.symm y) v z ?_
    rw [hz]
    symm
    apply hlvl

    apply hbij.1
    rw [pointsMap_pointsMkAdd, hψ, ← he, LinearEquiv.apply_symm_apply]

end Generic

section Base

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem isIntegral_ringOfIntegers : Algebra.IsIntegral ℤ_[p] (PadicAlgCl.ringOfIntegers p K) :=
  ⟨fun x => (isIntegral_algebraMap_iff (A := PadicAlgCl.ringOfIntegers p K) (B := PadicAlgCl p)
    Subtype.val_injective).1 (PadicAlgCl.ringOfIntegers.isIntegral_coe x)⟩

theorem norm_ιR_le_one (c : OR p (PadicAlgCl.ringOfIntegers p K)) :
    ‖ιR p (PadicAlgCl.ringOfIntegers p K) c‖ ≤ 1 := by
  haveI := isIntegral_ringOfIntegers p K
  rw [ιR_apply, PadicComplex.norm_extends]
  exact PadicAlgCl.ringOfIntegers.norm_le_one_of_isIntegral p
    (isIntegral_trans (A := PadicAlgCl.ringOfIntegers p K) _ c.2)

variable [FiniteDimensional ℚ_[p] K]

theorem tower {h : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h) {n : ℕ}
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

end PDivDAlphaK

open PDivDAlphaK in

theorem solution
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} {G G' : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h} (D : G.CartierDuality G')
    {n : ℕ} (hn : G.HasDimension n)
    (b : Module.Basis (Fin n) (PadicAlgCl.ringOfIntegers p K) G.cotangentModule) :
    ∃ dα : Fin n → (TateModule p (G'.Points (PadicAlgCl p)) →+ ℂ_[p]),
      (∀ (j : Fin n) (a : ℤ_[p]) (y : TateModule p (G'.Points (PadicAlgCl p))),
          dα j (a • y) = (a : ℚ_[p]) • dα j y) ∧
      (∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
          (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p),
          (∀ x : PadicAlgCl p, τ x = σ x) →
          ∀ (j : Fin n) (y : TateModule p (G'.Points (PadicAlgCl p))),
          dα j (G'.tateModuleRep (PadicAlgCl p) τ y) = σ • dα j y) ∧
      (∀ (j : Fin n) (y : TateModule p (G'.Points (PadicAlgCl p))) (v : ℕ)
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
              (p : ℝ) ^ (-(v : ℤ))) :=
  exists_dα p (norm_ιR_le_one p K) D (tower p K G hn) b

end S_PDivisibleGroup_CartierDuality_exists_addMonoidHom_tateModule_padicComplex_smul_eq_and_norm_sub_le_of_ringOfIntegers
end P2MW
export P2MW.S_PDivisibleGroup_CartierDuality_exists_addMonoidHom_tateModule_padicComplex_smul_eq_and_norm_sub_le_of_ringOfIntegers (solution)
