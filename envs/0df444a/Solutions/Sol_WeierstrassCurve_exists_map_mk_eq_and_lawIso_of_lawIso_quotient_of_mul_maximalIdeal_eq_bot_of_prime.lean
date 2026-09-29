-- Prove2me | solution 1 for WeierstrassCurve.exists_map_mk_eq_and_lawIso_of_lawIso_quotient_of_mul_maximalIdeal_eq_bot_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/a0191714-5166-5baf-b4af-79f880a0187d

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Theorems.Thm_WeierstrassCurve_exists_map_mk_eq_and_coeff_nthSeries_sub_eq_of_mul_maximalIdeal_eq_bot_of_prime
import Theorems.Thm_FormalGroup_exists_lawIso_of_coeff_nthSeries_eq_of_mul_maximalIdeal_eq_bot
import Theorems.Thm_FormalGroup_exists_lawIso_series_eq_of_isUnit_coeff_one
import Theorems.Thm_FormalGroup_LawIso_exists_symm_subst_eq_X
import Theorems.Thm_FormalGroup_LawHom_exists_comp_series_eq_subst
import Theorems.Thm_FormalGroup_LawHom_exists_isBaseChange_series_eq_map
import Theorems.Thm_FormalGroup_IsBaseChange_nthSeries_eq_map
import Theorems.Thm_WeierstrassCurve_formalW_map_and_formalGroupLawFixed_map
import Theorems.Thm_WeierstrassCurve_formalGroupLawFixed_comm_of_commRing
import Theorems.Thm_WeierstrassCurve_eq_zero_of_firstOrderVariableChange_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_map_mk_eq_and_lawIso_of_lawIso_quotient_of_mul_maximalIdeal_eq_bot_of_prime
p2m_attr_erase "instance" "MvFormalGroup.instIsCommOfFormalGroup MvFormalGroup.instIsCommAddMv MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing"
p2m_attr_erase "simp" "ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ MvFormalGroup.e3_one MvFormalGroup.e3_zero MvFormalGroup.e3_two MvFormalGroup.e2_one MvFormalGroup.e2_zero FormalGroup.LawHom.ofMvHom_series MvFormalGroup.e1_apply FormalGroup.LawHom.toMvHom_toPowerSeries MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast"
p2m_attr_erase "simp" "MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg'"

set_option autoImplicit false

open FormalGroup IsLocalRing

namespace H2Aux

open TrivSqZeroExt

variable {k : Type} [Field k]

noncomputable def Cinf (μ ρ ς τ : k) : WeierstrassCurve.VariableChange (TrivSqZeroExt k k) where
  u := Units.mkOfMulEqOne (1 - inr μ) (1 + inr μ) (by
    rw [mul_add, sub_mul, sub_mul, one_mul, one_mul, mul_one, inr_mul_inr, sub_zero, sub_add_cancel])
  r := inr ρ
  s := inr ς
  t := inr τ

theorem Cinf_uinv (μ ρ ς τ : k) : (((Cinf μ ρ ς τ).u⁻¹ : (TrivSqZeroExt k k)ˣ) : TrivSqZeroExt k k) = inl 1 + inr μ := by
  show (1 : TrivSqZeroExt k k) + inr μ = inl 1 + inr μ
  rw [inl_one]

theorem Cinf_u (μ ρ ς τ : k) : (((Cinf μ ρ ς τ).u : (TrivSqZeroExt k k)ˣ) : TrivSqZeroExt k k) = inl 1 - inr μ := by
  show (1 : TrivSqZeroExt k k) - inr μ = inl 1 - inr μ
  rw [inl_one]

theorem Cinf_map_fst (μ ρ ς τ : k) :
    (Cinf μ ρ ς τ).map (TrivSqZeroExt.fstHom k k k).toRingHom = 1 := by
  apply WeierstrassCurve.VariableChange.ext
  · apply Units.ext
    show (TrivSqZeroExt.fstHom k k k).toRingHom (((Cinf μ ρ ς τ).u : (TrivSqZeroExt k k)ˣ) : TrivSqZeroExt k k) = 1
    rw [Cinf_u]; show fst (inl (1 : k) - inr μ) = 1
    rw [fst_sub, fst_inl, fst_inr, sub_zero]
  · show fst (inr ρ : TrivSqZeroExt k k) = 0; exact fst_inr _ _
  · show fst (inr ς : TrivSqZeroExt k k) = 0; exact fst_inr _ _
  · show fst (inr τ : TrivSqZeroExt k k) = 0; exact fst_inr _ _

theorem inl_add_inr_pow (a μ : k) (n : ℕ) :
    (inl a + inr μ : TrivSqZeroExt k k) ^ n = inl (a ^ n) + inr (n * a ^ (n - 1) * μ) := by
  induction n with
  | zero => simp [← inl_one]
  | succ n ih =>
    rw [pow_succ, ih]
    apply TrivSqZeroExt.ext
    · simp only [fst_mul, fst_add, fst_inl, fst_inr, _root_.add_zero, pow_succ]
    · simp only [snd_mul, snd_add, snd_inl, snd_inr, _root_.zero_add, fst_add, fst_inl, fst_inr, _root_.add_zero, smul_eq_mul,
        MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, Nat.cast_succ, Nat.succ_sub_one]
      rcases n with _ | n
      · simp
      · simp only [Nat.succ_sub_one, Nat.cast_succ, pow_succ]; ring

theorem Cinf_smul (E₀ : WeierstrassCurve k) (μ ρ ς τ : k) :
    Cinf μ ρ ς τ • (E₀.map (algebraMap k (TrivSqZeroExt k k))) =
      ⟨inl E₀.a₁ + inr (E₀.a₁ * μ + 2 * ς),
       inl E₀.a₂ + inr (2 * E₀.a₂ * μ + 3 * ρ - E₀.a₁ * ς),
       inl E₀.a₃ + inr (3 * E₀.a₃ * μ + E₀.a₁ * ρ + 2 * τ),
       inl E₀.a₄ + inr (4 * E₀.a₄ * μ + 2 * E₀.a₂ * ρ - E₀.a₃ * ς - E₀.a₁ * τ),
       inl E₀.a₆ + inr (6 * E₀.a₆ * μ + E₀.a₄ * ρ - E₀.a₃ * τ)⟩ := by
  have hinl : ∀ x : k, algebraMap k (TrivSqZeroExt k k) x = inl x := fun x => congrFun (algebraMap_eq_inl k k) x
  have hU : ∀ n : ℕ, (((Cinf μ ρ ς τ).u⁻¹ : (TrivSqZeroExt k k)ˣ) : TrivSqZeroExt k k) ^ n =
      inl 1 + inr ((n : k) * μ) := by
    intro n; rw [Cinf_uinv, inl_add_inr_pow, one_pow, one_pow, mul_one]
  have hU1 : (((Cinf μ ρ ς τ).u⁻¹ : (TrivSqZeroExt k k)ˣ) : TrivSqZeroExt k k) = inl 1 + inr ((1 : k) * μ) := by
    rw [← pow_one (((Cinf μ ρ ς τ).u⁻¹ : (TrivSqZeroExt k k)ˣ) : TrivSqZeroExt k k), hU, Nat.cast_one]
  have hn : ∀ n : ℕ, [OfNat (TrivSqZeroExt k k) n] → [OfNat k n] → True := fun _ _ _ => trivial
  have h2 : (2 : TrivSqZeroExt k k) = inl 2 := ((map_ofNat (algebraMap k (TrivSqZeroExt k k)) 2).symm).trans (hinl 2)
  have h3 : (3 : TrivSqZeroExt k k) = inl 3 := ((map_ofNat (algebraMap k (TrivSqZeroExt k k)) 3).symm).trans (hinl 3)
  have hr : (Cinf μ ρ ς τ).r = inr ρ := rfl
  have hs : (Cinf μ ρ ς τ).s = inr ς := rfl
  have ht : (Cinf μ ρ ς τ).t = inr τ := rfl
  refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_
  all_goals
    simp only [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂, WeierstrassCurve.variableChange_a₃,
      WeierstrassCurve.variableChange_a₄, WeierstrassCurve.variableChange_a₆, WeierstrassCurve.map, hinl, hU, hr, hs, ht, h2, h3]
    try rw [hU1]
    apply TrivSqZeroExt.ext
    · simp only [pow_two, pow_three, fst_mul, fst_add, fst_sub, fst_neg, fst_inl, fst_inr, smul_eq_mul,
        MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
      ring
    · simp only [pow_two, pow_three, snd_mul, snd_add, snd_sub, snd_neg, snd_inl, snd_inr, fst_mul, fst_add, fst_sub,
        fst_neg, fst_inl, fst_inr, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
      ring

noncomputable def tangentMap (E₀ : WeierstrassCurve k) : (Fin 4 → k) →ₗ[k] (Fin 5 → k) where
  toFun m := ![E₀.a₁ * m 0 + 2 * m 2, 2 * E₀.a₂ * m 0 + 3 * m 1 - E₀.a₁ * m 2,
    3 * E₀.a₃ * m 0 + E₀.a₁ * m 1 + 2 * m 3, 4 * E₀.a₄ * m 0 + 2 * E₀.a₂ * m 1 - E₀.a₃ * m 2 - E₀.a₁ * m 3,
    6 * E₀.a₆ * m 0 + E₀.a₄ * m 1 - E₀.a₃ * m 3]
  map_add' m m' := by ext i; fin_cases i <;> simp <;> ring
  map_smul' r m := by ext i; fin_cases i <;> simp <;> ring

theorem tangentMap_apply (E₀ : WeierstrassCurve k) (m : Fin 4 → k) :
    tangentMap E₀ m = ![E₀.a₁ * m 0 + 2 * m 2, 2 * E₀.a₂ * m 0 + 3 * m 1 - E₀.a₁ * m 2,
      3 * E₀.a₃ * m 0 + E₀.a₁ * m 1 + 2 * m 3, 4 * E₀.a₄ * m 0 + 2 * E₀.a₂ * m 1 - E₀.a₃ * m 2 - E₀.a₁ * m 3,
      6 * E₀.a₆ * m 0 + E₀.a₄ * m 1 - E₀.a₃ * m 3] := rfl

theorem tangentMap_injective (E₀ : WeierstrassCurve k) [E₀.IsElliptic] : Function.Injective (tangentMap E₀) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro m hm
  rw [LinearMap.mem_ker, tangentMap_apply] at hm
  have h0 := congrFun hm 0; have h1 := congrFun hm 1; have h2 := congrFun hm 2; have h3 := congrFun hm 3
  have h4 := congrFun hm 4
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Pi.zero_apply] at h0 h1 h2 h3 h4
  obtain ⟨e0, e1, e2, e3⟩ := WeierstrassCurve.eq_zero_of_firstOrderVariableChange_eq_zero k E₀ (m 0) (m 1) (m 2) (m 3)
    (by linear_combination h0) (by linear_combination h1) (by linear_combination h2) (by linear_combination h3)
    (by linear_combination h4)
  funext i; fin_cases i <;> assumption

noncomputable def functional (c : Fin 5 → k) : (Fin 5 → k) →ₗ[k] k := ∑ i, c i • LinearMap.proj i

theorem functional_apply (c δ : Fin 5 → k) : functional c δ = ∑ i, c i * δ i := by
  simp only [functional, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]

theorem range_eq_ker (L : (Fin 4 → k) →ₗ[k] (Fin 5 → k)) (hL : Function.Injective L) (lam : (Fin 5 → k) →ₗ[k] k)
    (hcomp : LinearMap.range L ≤ LinearMap.ker lam) (v : Fin 5 → k) (hv : lam v ≠ 0) :
    LinearMap.range L = LinearMap.ker lam := by
  have hsurj : Function.Surjective lam := by
    intro t
    refine ⟨(t / lam v) • v, ?_⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ t hv]
  have hfr : Module.finrank k (LinearMap.range L) = 4 := by
    rw [LinearMap.finrank_range_of_inj hL, Module.finrank_fin_fun]
  have hfk : Module.finrank k (LinearMap.ker lam) = 4 := by
    have h := LinearMap.finrank_range_add_finrank_ker lam
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h
    omega
  exact Submodule.eq_of_le_of_finrank_eq hcomp (by rw [hfr, hfk])

end H2Aux

namespace L2Aux

open TrivSqZeroExt

variable {R : Type} [CommRing R]

theorem inl_add_inr_pow {M : Type} [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
    (a : R) (m : M) (n : ℕ) :
    (inl a + inr m : TrivSqZeroExt R M) ^ n = inl (a ^ n) + inr (((n : R) * a ^ (n - 1)) • m) := by
  induction n with
  | zero => simp [← inl_one]
  | succ n ih =>
    rw [pow_succ, ih]
    apply TrivSqZeroExt.ext
    · simp only [fst_mul, fst_add, fst_inl, fst_inr, _root_.add_zero, pow_succ]
    · simp only [snd_mul, snd_add, snd_inl, snd_inr, _root_.zero_add, fst_add, fst_inl, fst_inr, _root_.add_zero,
        MulOpposite.smul_eq_mul_unop, op_smul_eq_smul, smul_smul, ← add_smul, Nat.cast_succ, Nat.succ_sub_one]
      congr 1
      rcases n with _ | n
      · simp
      · simp only [Nat.succ_sub_one, Nat.cast_succ, pow_succ]; ring

noncomputable def Cu : WeierstrassCurve.VariableChange (TrivSqZeroExt R (Fin 4 → R)) where
  u := Units.mkOfMulEqOne (1 - inr (Pi.single 0 1)) (1 + inr (Pi.single 0 1)) (by
    rw [mul_add, sub_mul, sub_mul, one_mul, one_mul, mul_one, inr_mul_inr, sub_zero, sub_add_cancel])
  r := inr (Pi.single 1 1)
  s := inr (Pi.single 2 1)
  t := inr (Pi.single 3 1)

theorem Cu_uinv : (((Cu (R := R)).u⁻¹ : (TrivSqZeroExt R (Fin 4 → R))ˣ) : TrivSqZeroExt R (Fin 4 → R)) =
    inl 1 + inr (Pi.single 0 1) := by
  show (1 : TrivSqZeroExt R (Fin 4 → R)) + inr (Pi.single 0 1) = inl 1 + inr (Pi.single 0 1)
  rw [inl_one]

theorem Cu_u : (((Cu (R := R)).u : (TrivSqZeroExt R (Fin 4 → R))ˣ) : TrivSqZeroExt R (Fin 4 → R)) =
    inl 1 - inr (Pi.single 0 1) := by
  show (1 : TrivSqZeroExt R (Fin 4 → R)) - inr (Pi.single 0 1) = inl 1 - inr (Pi.single 0 1)
  rw [inl_one]

noncomputable def CuW (W : WeierstrassCurve R) : WeierstrassCurve (TrivSqZeroExt R (Fin 4 → R)) :=
  Cu (R := R) • (W.map (algebraMap R (TrivSqZeroExt R (Fin 4 → R))))

theorem Cu_smul_fst_snd (W : WeierstrassCurve R) :
    let W' := CuW W
    (W'.a₁.fst = W.a₁ ∧ W'.a₂.fst = W.a₂ ∧ W'.a₃.fst = W.a₃ ∧ W'.a₄.fst = W.a₄ ∧ W'.a₆.fst = W.a₆) ∧
    (W'.a₁.snd = ![W.a₁, 0, 2, 0] ∧
     W'.a₂.snd = ![2 * W.a₂, 3, -W.a₁, 0] ∧
     W'.a₃.snd = ![3 * W.a₃, W.a₁, 0, 2] ∧
     W'.a₄.snd = ![4 * W.a₄, 2 * W.a₂, -W.a₃, -W.a₁] ∧
     W'.a₆.snd = ![6 * W.a₆, W.a₄, 0, -W.a₃]) := by
  have hinl : ∀ x : R, algebraMap R (TrivSqZeroExt R (Fin 4 → R)) x = inl x :=
    fun x => congrFun (algebraMap_eq_inl R (Fin 4 → R)) x
  have hU : ∀ n : ℕ, (((Cu (R := R)).u⁻¹ : (TrivSqZeroExt R (Fin 4 → R))ˣ) : TrivSqZeroExt R (Fin 4 → R)) ^ n =
      inl 1 + inr ((n : R) • Pi.single (0 : Fin 4) (1 : R)) := by
    intro n; rw [Cu_uinv, inl_add_inr_pow, one_pow, one_pow, mul_one]
  have hU1 : (((Cu (R := R)).u⁻¹ : (TrivSqZeroExt R (Fin 4 → R))ˣ) : TrivSqZeroExt R (Fin 4 → R)) =
      inl 1 + inr (((1 : ℕ) : R) • Pi.single (0 : Fin 4) (1 : R)) := by
    rw [← pow_one (((Cu (R := R)).u⁻¹ : (TrivSqZeroExt R (Fin 4 → R))ˣ) : TrivSqZeroExt R (Fin 4 → R)), hU]
  have h2 : (2 : TrivSqZeroExt R (Fin 4 → R)) = inl 2 :=
    ((map_ofNat (algebraMap R (TrivSqZeroExt R (Fin 4 → R))) 2).symm).trans (hinl 2)
  have h3 : (3 : TrivSqZeroExt R (Fin 4 → R)) = inl 3 :=
    ((map_ofNat (algebraMap R (TrivSqZeroExt R (Fin 4 → R))) 3).symm).trans (hinl 3)
  have hr : (Cu (R := R)).r = inr (Pi.single 1 1) := rfl
  have hs : (Cu (R := R)).s = inr (Pi.single 2 1) := rfl
  have ht : (Cu (R := R)).t = inr (Pi.single 3 1) := rfl
  simp only [CuW, WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂, WeierstrassCurve.variableChange_a₃,
    WeierstrassCurve.variableChange_a₄, WeierstrassCurve.variableChange_a₆, WeierstrassCurve.map, hinl, hU, hr, hs, ht,
    h2, h3]
  rw [Cu_uinv]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  iterate 5
    · simp only [pow_two, pow_three, fst_mul, fst_add, fst_sub, fst_neg, fst_inl, fst_inr]
      ring
  all_goals
    funext j
    simp only [pow_two, pow_three, snd_mul, snd_add, snd_sub, snd_neg, snd_inl, snd_inr, fst_mul, fst_add,
      fst_sub, fst_neg, fst_inl, fst_inr, op_smul_eq_smul, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply,
      Pi.zero_apply, smul_eq_mul, smul_zero, _root_.zero_add, _root_.add_zero, mul_one, one_mul, mul_zero, zero_mul]
    fin_cases j <;> simp <;> ring

end L2Aux

namespace L2Aux

open TrivSqZeroExt

def LEmat {T : Type} [CommRing T] (E : WeierstrassCurve T) : Matrix (Fin 5) (Fin 4) T :=
  !![E.a₁, 0, 2, 0; 2 * E.a₂, 3, -E.a₁, 0; 3 * E.a₃, E.a₁, 0, 2; 4 * E.a₄, 2 * E.a₂, -E.a₃, -E.a₁;
    6 * E.a₆, E.a₄, 0, -E.a₃]

theorem exists_variableChange_smul_eq {T : Type} [CommRing T] (E : WeierstrassCurve T) (m : Fin 4 → T)
    (hm : ∀ i j, m i * m j = 0) :
    ∃ C : WeierstrassCurve.VariableChange T,
      ((C.u : Tˣ) : T) = 1 - m 0 ∧ C.r = m 1 ∧ C.s = m 2 ∧ C.t = m 3 ∧
      C • E = ⟨E.a₁ + (LEmat E).mulVec m 0, E.a₂ + (LEmat E).mulVec m 1, E.a₃ + (LEmat E).mulVec m 2,
        E.a₄ + (LEmat E).mulVec m 3, E.a₆ + (LEmat E).mulVec m 4⟩ := by
  classical
  let U := TrivSqZeroExt T (Fin 4 → T)
  let g : (Fin 4 → T) →ₗ[T] T :=
    { toFun := fun v => ∑ j, v j * m j
      map_add' := fun v v' => by
        rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _ => by rw [Pi.add_apply, add_mul]
      map_smul' := fun r v => by
        rw [RingHom.id_apply, Finset.smul_sum]; exact Finset.sum_congr rfl fun j _ => by
          rw [Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc] }
  have hg : ∀ v, g v = ∑ j, v j * m j := fun v => rfl
  have hgg : ∀ x y, g x * g y = 0 := by
    intro x y; rw [hg, hg, Finset.sum_mul_sum]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    calc x i * m i * (y j * m j) = x i * y j * (m i * m j) := by ring
      _ = 0 := by rw [hm, mul_zero]
  let Θ : U →ₐ[T] T := TrivSqZeroExt.lift (Algebra.ofId T T) g hgg
    (by
      intro r x
      rw [hg, hg, Algebra.ofId_apply, Algebra.algebraMap_self, RingHom.id_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, mul_assoc])
    (by
      intro r x
      rw [hg, hg, Algebra.ofId_apply, Algebra.algebraMap_self, RingHom.id_apply, Finset.sum_mul, op_smul_eq_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.smul_apply, smul_eq_mul]; ring)
  have hΘ : ∀ x : U, Θ x = x.fst + ∑ j, x.snd j * m j := by
    intro x
    conv_lhs => rw [← inl_fst_add_inr_snd_eq x]
    rw [map_add, lift_apply_inl, lift_apply_inr, Algebra.ofId_apply, Algebra.algebraMap_self, RingHom.id_apply, hg]
  have hΘalg : Θ.toRingHom.comp (algebraMap T U) = RingHom.id T := RingHom.ext fun x => Θ.commutes x
  refine ⟨(Cu (R := T)).map Θ.toRingHom, ?_, ?_, ?_, ?_, ?_⟩
  · show Θ (((Cu (R := T)).u : Uˣ) : U) = 1 - m 0
    rw [Cu_u, hΘ, fst_sub, fst_inl, fst_inr, sub_zero, snd_sub, snd_inl, snd_inr, zero_sub]
    simp [Finset.sum_neg_distrib, Pi.single_apply, sub_eq_add_neg]
  · show Θ (inr (Pi.single 1 1)) = m 1
    rw [hΘ, fst_inr, snd_inr, _root_.zero_add]; simp [Pi.single_apply]
  · show Θ (inr (Pi.single 2 1)) = m 2
    rw [hΘ, fst_inr, snd_inr, _root_.zero_add]; simp [Pi.single_apply]
  · show Θ (inr (Pi.single 3 1)) = m 3
    rw [hΘ, fst_inr, snd_inr, _root_.zero_add]; simp [Pi.single_apply]
  · have hE : E = (E.map (algebraMap T U)).map Θ.toRingHom := by
      rw [WeierstrassCurve.map_map, hΘalg, WeierstrassCurve.map_id]
    conv_lhs => rw [hE, WeierstrassCurve.map_variableChange]
    obtain ⟨⟨f1, f2, f3, f4, f6⟩, ⟨s1, s2, s3, s4, s6⟩⟩ := Cu_smul_fst_snd E
    rw [show Cu (R := T) • E.map (algebraMap T U) = CuW E from rfl]
    refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_
    · show Θ (CuW E).a₁ = _
      rw [hΘ, f1, s1]; unfold LEmat; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four]; try ring
    · show Θ (CuW E).a₂ = _
      rw [hΘ, f2, s2]; unfold LEmat; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four]; try ring
    · show Θ (CuW E).a₃ = _
      rw [hΘ, f3, s3]; unfold LEmat; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four]; try ring
    · show Θ (CuW E).a₄ = _
      rw [hΘ, f4, s4]; unfold LEmat; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four]; try ring
    · show Θ (CuW E).a₆ = _
      rw [hΘ, f6, s6]; unfold LEmat; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four]; try ring

end L2Aux

namespace L2Aux

theorem exists_law (S : Type) [CommRing S] (W : WeierstrassCurve S) (hW : IsUnit W.Δ) :
    ∃ G : FormalGroup S, G.toPowerSeries = W.formalGroupLawFixed := by
  classical
  let P := MvPolynomial (Fin 5) ℤ
  let Wu : WeierstrassCurve P :=
    ⟨MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, MvPolynomial.X 3, MvPolynomial.X 4⟩
  have hΔ0 : Wu.Δ ≠ 0 := by
    intro h
    have h1 : (Wu.map (MvPolynomial.eval (![0, 0, 0, -1, 0] : Fin 5 → ℤ))).Δ = 0 := by
      rw [WeierstrassCurve.map_Δ, h, map_zero]
    have h2 : Wu.map (MvPolynomial.eval (![0, 0, 0, -1, 0] : Fin 5 → ℤ)) = ⟨0, 0, 0, -1, 0⟩ := by
      refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_ <;>
      · show MvPolynomial.eval _ (MvPolynomial.X _) = _
        rw [MvPolynomial.eval_X]; rfl
    rw [h2] at h1
    revert h1
    norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  obtain ⟨D, hD⟩ : ∃ D : P, Wu.Δ = D := ⟨_, rfl⟩
  have hpow : Submonoid.powers D ≤ nonZeroDivisors P := powers_le_nonZeroDivisors_of_noZeroDivisors (hD ▸ hΔ0)
  let A := Localization.Away D
  haveI : IsDomain A := IsLocalization.isDomain_localization hpow
  let WA : WeierstrassCurve A := Wu.map (algebraMap P A)
  have hΔA : IsUnit WA.Δ := by
    rw [WeierstrassCurve.map_Δ, hD]; exact IsLocalization.Away.algebraMap_isUnit D
  haveI : WA.IsElliptic := ⟨hΔA⟩
  let φ₀ : P →+* S := MvPolynomial.eval₂Hom (Int.castRingHom S) ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]
  have hφ₀W : Wu.map φ₀ = W := by
    refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_ <;>
    · show MvPolynomial.eval₂Hom (Int.castRingHom S) _ (MvPolynomial.X _) = _
      rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]; rfl
  have hφ₀Δ : IsUnit (φ₀ D) := by rw [← hD, ← WeierstrassCurve.map_Δ, hφ₀W]; exact hW
  let φ : A →+* S := IsLocalization.Away.lift D hφ₀Δ
  have hWφ : WA.map φ = W := by rw [WeierstrassCurve.map_map, IsLocalization.Away.lift_comp, hφ₀W]
  refine ⟨WA.formalGroup.map φ, ?_⟩
  rw [FormalGroup.map_toPowerSeries, ← hWφ, (WeierstrassCurve.formalW_map_and_formalGroupLawFixed_map WA φ).2]; rfl

theorem LEmat_mulVec {k : Type} [Field k] (E₀ : WeierstrassCurve k) (m : Fin 4 → k) :
    (LEmat E₀).mulVec m = H2Aux.tangentMap E₀ m := by
  rw [H2Aux.tangentMap_apply]
  unfold LEmat
  funext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> ring

theorem exists_leftInverse_defect {k : Type} [Field k] (L : (Fin 4 → k) →ₗ[k] (Fin 5 → k)) (hL : Function.Injective L)
    (lam : (Fin 5 → k) →ₗ[k] k) (hker : LinearMap.range L = LinearMap.ker lam) (v : Fin 5 → k) (hv : lam v = 1) :
    ∃ (g : (Fin 5 → k) →ₗ[k] (Fin 4 → k)) (w : Fin 5 → k), ∀ x, L (g x) - x = lam x • w := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective L (LinearMap.ker_eq_bot.mpr hL)
  refine ⟨g, L (g v) - v, fun x => ?_⟩
  have hLg : ∀ y, lam y = 0 → L (g y) = y := by
    intro y hy
    have : y ∈ LinearMap.range L := by rw [hker]; exact hy
    obtain ⟨z, rfl⟩ := this
    rw [show g (L z) = z from congrFun (congrArg DFunLike.coe hg) z]
  have h1 : lam (x - lam x • v) = 0 := by rw [map_sub, map_smul, hv, smul_eq_mul, mul_one, sub_self]
  have h2 := hLg _ h1
  rw [map_sub, map_smul, map_sub, map_smul] at h2
  rw [smul_sub]
  linear_combination (exp := 1) h2

theorem lift_solve {k T : Type} [Field k] [CommRing T] [IsLocalRing T] (I : Ideal T)
    (hI : I * IsLocalRing.maximalIdeal T = ⊥) (resT : T →+* k) (hres : Function.Surjective resT)
    (hker : RingHom.ker resT = IsLocalRing.maximalIdeal T)
    (L₀ : Matrix (Fin 5) (Fin 4) k) (LT : Matrix (Fin 5) (Fin 4) T) (hL : ∀ i j, resT (LT i j) = L₀ i j)
    (c : Fin 5 → k) (t : Fin 5 → T) (ht : ∀ i, resT (t i) = c i)
    (G₀ : Matrix (Fin 4) (Fin 5) k) (w : Fin 5 → k) (hid : ∀ i l, (L₀ * G₀) i l - (1 : Matrix (Fin 5) (Fin 5) k) i l = w i * c l)
    (δ : Fin 5 → T) (hδ : ∀ i, δ i ∈ I) (hsum : ∑ i, t i * δ i = 0) :
    ∃ m : Fin 4 → T, (∀ j, m j ∈ I) ∧ LT.mulVec m = δ := by
  classical
  choose Γf hΓ using fun (p : Fin 4 × Fin 5) => hres (G₀ p.1 p.2)
  choose ωf hω using fun i : Fin 5 => hres (w i)
  let Γ : Matrix (Fin 4) (Fin 5) T := fun j l => Γf (j, l)
  have hmem : ∀ x : T, x ∈ IsLocalRing.maximalIdeal T ↔ resT x = 0 := fun x => by rw [← hker, RingHom.mem_ker]
  have hmI : ∀ a b : T, a ∈ IsLocalRing.maximalIdeal T → b ∈ I → a * b = 0 := by
    intro a b ha hb
    have : b * a ∈ I * IsLocalRing.maximalIdeal T := Ideal.mul_mem_mul hb ha
    rw [hI, Ideal.mem_bot] at this; rwa [mul_comm] at this

  have hC : ∀ i l, (LT * Γ) i l - (1 : Matrix (Fin 5) (Fin 5) T) i l - ωf i * t l ∈ IsLocalRing.maximalIdeal T := by
    intro i l
    rw [hmem, map_sub, map_sub, map_mul, hω, ht, Matrix.mul_apply, map_sum]
    have e1 : ∑ j, resT (LT i j * Γ j l) = (L₀ * G₀) i l := by
      rw [Matrix.mul_apply]; refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, hL]; show _ * resT (Γf (j, l)) = _; rw [hΓ]
    have e2 : resT ((1 : Matrix (Fin 5) (Fin 5) T) i l) = (1 : Matrix (Fin 5) (Fin 5) k) i l := by
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    rw [e1, e2, hid i l, sub_self]
  refine ⟨Γ.mulVec δ, fun j => ?_, ?_⟩
  · rw [Matrix.mulVec, dotProduct]
    exact I.sum_mem fun l _ => I.mul_mem_left _ (hδ l)
  · rw [Matrix.mulVec_mulVec]
    funext i
    rw [Matrix.mulVec, dotProduct]
    have : ∀ l, (LT * Γ) i l * δ l = (1 : Matrix (Fin 5) (Fin 5) T) i l * δ l + ωf i * (t l * δ l) := by
      intro l
      have h0 := hmI _ _ (hC i l) (hδ l)
      linear_combination h0
    rw [Finset.sum_congr rfl fun l _ => this l, Finset.sum_add_distrib, ← Finset.mul_sum, hsum, mul_zero, _root_.add_zero,
      Finset.sum_eq_single i]
    · rw [Matrix.one_apply_eq, one_mul]
    · intro l _ hl; rw [Matrix.one_apply_ne' hl, zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h

end L2Aux

theorem solution
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
    (E₀ : WeierstrassCurve k) [E₀.IsElliptic] (hE₀ : E₀.formalGroup.IsDrinfeldBasisAdic ⊥ q 0 0)
    (T : Type) [CommRing T] [IsLocalRing T] (I : Ideal T) (hI : I * maximalIdeal T = ⊥) (hIm : I ≤ maximalIdeal T)
    (resT : T →+* k) (hresT : Function.Surjective resT) (hkerT : RingHom.ker resT = maximalIdeal T)

    (G : FormalGroup T) [G.IsComm] (hG : G.IsBaseChange resT E₀.formalGroup)
    (E₁ : WeierstrassCurve T) (hE₁ : E₁.map resT = E₀)
    (G₁ : FormalGroup T) [G₁.IsComm] (hG₁ : G₁.toPowerSeries = E₁.formalGroupLawFixed)

    (Gbar G₁bar : FormalGroup (T ⧸ I))
    (hGbar : G.IsBaseChange (Ideal.Quotient.mk I) Gbar) (hG₁bar : G₁.IsBaseChange (Ideal.Quotient.mk I) G₁bar)
    (ψbar : FormalGroup.LawIso G₁bar Gbar)
    (hψbar : ∀ m : ℕ, PowerSeries.coeff m ψbar.series - (if m = 1 then 1 else 0) ∈
      (maximalIdeal T).map (Ideal.Quotient.mk I)) :
    ∃ (E : WeierstrassCurve T) (_ : E.map (Ideal.Quotient.mk I) = E₁.map (Ideal.Quotient.mk I))
      (G' : FormalGroup T) (_ : G'.toPowerSeries = E.formalGroupLawFixed) (ψ : FormalGroup.LawIso G' G),
      ∀ m : ℕ, resT (PowerSeries.coeff m ψ.series) = if m = 1 then 1 else 0 := by
  classical
  have hmem : ∀ x : T, x ∈ maximalIdeal T ↔ resT x = 0 := fun x => by rw [← hkerT, RingHom.mem_ker]
  set πI : T →+* T ⧸ I := Ideal.Quotient.mk I with hπI
  have hπIsurj : Function.Surjective πI := Ideal.Quotient.mk_surjective
  have hkerI : ∀ x : T, πI x = 0 ↔ x ∈ I := fun x => by rw [hπI, Ideal.Quotient.eq_zero_iff_mem]

  set a : PowerSeries (T ⧸ I) := ψbar.series with ha
  have ha0 : PowerSeries.constantCoeff a = 0 := ψbar.constantCoeff_series
  choose sc hsc using fun m : ℕ => hπIsurj (PowerSeries.coeff m a)
  set s : PowerSeries T := PowerSeries.mk fun m => if m = 0 then 0 else sc m with hs
  have hs0 : PowerSeries.constantCoeff s = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hs, PowerSeries.coeff_mk, if_pos rfl]
  have hsmap : PowerSeries.map πI s = a := by
    ext m
    rw [PowerSeries.coeff_map, hs, PowerSeries.coeff_mk]
    by_cases hm : m = 0
    · subst hm; rw [if_pos rfl, map_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply, ha0]
    · rw [if_neg hm, hsc]
  have hsm : ∀ m : ℕ, PowerSeries.coeff m s - (if m = 1 then 1 else 0) ∈ maximalIdeal T := by
    intro m
    have h1 : πI (PowerSeries.coeff m s - (if m = 1 then 1 else 0)) ∈ (maximalIdeal T).map πI := by
      rw [map_sub, ← PowerSeries.coeff_map, hsmap]
      convert hψbar m using 2
      split_ifs <;> simp
    obtain ⟨y, hy, hyx⟩ := (Ideal.mem_map_iff_of_surjective πI hπIsurj).mp h1
    have : PowerSeries.coeff m s - (if m = 1 then 1 else 0) - y ∈ I := by
      rw [← hkerI, map_sub, hyx, sub_self]
    have := (maximalIdeal T).add_mem (hIm this) hy
    rwa [sub_add_cancel] at this
  have hs1 : IsUnit (PowerSeries.coeff 1 s) := by
    by_contra hu
    have h1 : PowerSeries.coeff 1 s ∈ maximalIdeal T := (IsLocalRing.mem_maximalIdeal _).mpr hu
    have h2 := hsm 1
    rw [if_pos rfl] at h2
    have := (maximalIdeal T).sub_mem h1 h2
    rw [sub_sub_cancel] at this
    exact (maximalIdeal.isMaximal T).ne_top ((Ideal.eq_top_iff_one _).mpr this)
  set v : PowerSeries T := s.substInvOfIsUnit hs1 with hv
  have hv0 : PowerSeries.constantCoeff v = 0 := PowerSeries.constantCoeff_substInvOfIsUnit s hs1
  have hv1 : IsUnit (PowerSeries.coeff 1 v) := by
    rw [hv, PowerSeries.coeff_one_substInvOfIsUnit]; exact Units.isUnit _
  have hss : PowerSeries.HasSubst s := PowerSeries.HasSubst.of_constantCoeff_zero' hs0
  have hvs : PowerSeries.HasSubst v := PowerSeries.HasSubst.of_constantCoeff_zero' hv0
  have e_sv : PowerSeries.subst v s = PowerSeries.X := PowerSeries.subst_substInvOfIsUnit_right s hs0 hs1
  have e_vs : PowerSeries.subst s v = PowerSeries.X := PowerSeries.subst_substInvOfIsUnit_left s hs0 hs1

  have em : ∀ (S' : Type) [CommRing S'] (f : T →+* S') (p : PowerSeries T), MvPowerSeries.map f p = PowerSeries.map f p :=
    fun _ _ _ _ => rfl
  have hsres : PowerSeries.map resT s = PowerSeries.X := by
    ext m; rw [PowerSeries.coeff_map, PowerSeries.coeff_X]
    have := (hmem _).mp (hsm m); rw [map_sub, sub_eq_zero] at this
    rw [this]; split_ifs <;> simp
  have hmap_inv : ∀ (S' : Type) [CommRing S'] (f : T →+* S'),
      PowerSeries.subst (PowerSeries.map f s) (PowerSeries.map f v) = PowerSeries.X ∧
      PowerSeries.subst (PowerSeries.map f v) (PowerSeries.map f s) = PowerSeries.X := by
    intro S' _ f
    constructor
    · have := congrArg (PowerSeries.map f) e_vs
      rw [PowerSeries.map_X, ← em, PowerSeries.map_subst hss] at this
      try simp only [em] at this
      exact this
    · have := congrArg (PowerSeries.map f) e_sv
      rw [PowerSeries.map_X, ← em, PowerSeries.map_subst hvs] at this
      try simp only [em] at this
      exact this
  have hvres : PowerSeries.map resT v = PowerSeries.X := by
    have := (hmap_inv k resT).1
    rwa [hsres, PowerSeries.X_subst] at this

  obtain ⟨X, ⟨ξ, hξ⟩, hXc, -⟩ := FormalGroup.exists_lawIso_series_eq_of_isUnit_coeff_one G v hv0 hv1
  haveI : X.IsComm := hXc inferInstance
  obtain ⟨ξ', hξ1, hξ2⟩ := FormalGroup.LawIso.exists_symm_subst_eq_X ξ
  rw [hξ] at hξ1 hξ2
  have hξ's : ξ'.series = s := by
    have hξ's0 : PowerSeries.HasSubst ξ'.series := PowerSeries.HasSubst.of_constantCoeff_zero' ξ'.constantCoeff_series
    calc ξ'.series = PowerSeries.subst ξ'.series PowerSeries.X := (PowerSeries.subst_X hξ's0).symm
      _ = PowerSeries.subst ξ'.series (PowerSeries.subst v s) := by rw [e_sv]
      _ = PowerSeries.subst (PowerSeries.subst ξ'.series v) s := PowerSeries.subst_comp_subst_apply hvs hξ's0 s
      _ = s := by rw [hξ2, PowerSeries.X_subst]

  set Xbar : FormalGroup (T ⧸ I) := X.map πI with hXbar
  have hXbc : X.IsBaseChange πI Xbar := by
    show Xbar.toPowerSeries = MvPowerSeries.map πI X.toPowerSeries; rw [hXbar, FormalGroup.map_toPowerSeries]
  obtain ⟨ξb, hξb⟩ := FormalGroup.LawHom.exists_isBaseChange_series_eq_map πI ξ.toLawHom Gbar Xbar hGbar hXbc
  rw [show ξ.toLawHom.series = v from hξ] at hξb
  have hξb1 : IsUnit (PowerSeries.coeff 1 ξb.series) := by
    rw [hξb, PowerSeries.coeff_map]; exact hv1.map _
  obtain ⟨ψb', hp1, hp2⟩ := FormalGroup.LawIso.exists_symm_subst_eq_X ψbar
  have hab : PowerSeries.map πI s = a := hsmap
  have hvb : PowerSeries.subst a (PowerSeries.map πI v) = PowerSeries.X := by rw [← hab]; exact (hmap_inv _ πI).1
  have hp's : ψb'.series = PowerSeries.map πI v := by
    have hp0 : PowerSeries.HasSubst ψb'.series := PowerSeries.HasSubst.of_constantCoeff_zero' ψb'.constantCoeff_series
    have ha0' : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero' ha0
    symm
    calc PowerSeries.map πI v = PowerSeries.subst (PowerSeries.subst ψb'.series a) (PowerSeries.map πI v) := by
          rw [hp2, PowerSeries.X_subst]
      _ = PowerSeries.subst ψb'.series (PowerSeries.subst a (PowerSeries.map πI v)) :=
          (PowerSeries.subst_comp_subst_apply ha0' hp0 _).symm
      _ = ψb'.series := by rw [hvb, PowerSeries.subst_X hp0]
  have hvb0 : PowerSeries.constantCoeff (PowerSeries.map πI v) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      hv0, map_zero]
  have hvb1 : IsUnit (PowerSeries.coeff 1 (PowerSeries.map πI v)) := by rw [PowerSeries.coeff_map]; exact hv1.map _
  obtain ⟨Y, -, -, hYu⟩ := FormalGroup.exists_lawIso_series_eq_of_isUnit_coeff_one Gbar (PowerSeries.map πI v) hvb0 hvb1
  have hX1 : Xbar = Y := hYu Xbar ⟨⟨ξb, hξb1⟩, hξb⟩
  have hG1Y : G₁bar = Y := hYu G₁bar ⟨ψb', hp's⟩
  have hXG₁ : MvPowerSeries.map πI X.toPowerSeries = MvPowerSeries.map πI G₁.toPowerSeries := by
    have e1 : Xbar.toPowerSeries = G₁bar.toPowerSeries := by rw [hX1, hG1Y]
    rw [hXbar, FormalGroup.map_toPowerSeries] at e1
    rw [e1]; exact hG₁bar
  have hq_bc : ∀ n : ℕ, PowerSeries.coeff n (X.nthSeries q) - PowerSeries.coeff n (G₁.nthSeries q) ∈ I := by
    intro n
    rw [← hkerI, map_sub, ← PowerSeries.coeff_map, ← PowerSeries.coeff_map,
      ← FormalGroup.IsBaseChange.nthSeries_eq_map X πI Xbar hXbc q,
      ← FormalGroup.IsBaseChange.nthSeries_eq_map G₁ πI G₁bar hG₁bar q, hX1, hG1Y, sub_self]

  obtain ⟨E, hEE₁, hL1⟩ := WeierstrassCurve.exists_map_mk_eq_and_coeff_nthSeries_sub_eq_of_mul_maximalIdeal_eq_bot_of_prime q k E₀
    hE₀ T I hI hIm resT hresT hkerT E₁ hE₁ _ (hq_bc q)
  obtain ⟨d1, d2, d3, d4, d6⟩ := WeierstrassCurve.ext_iff.mp hEE₁
  obtain ⟨r1, r2, r3, r4, r6⟩ := WeierstrassCurve.ext_iff.mp hE₁
  have hqI : ∀ x y : T, Ideal.Quotient.mk I x = Ideal.Quotient.mk I y → x - y ∈ I := fun x y h => (Ideal.Quotient.eq).mp h
  have hEres : E.map resT = E₀ := by
    have key : ∀ x y : T, x - y ∈ I → resT x = resT y := by
      intro x y h; rw [← sub_eq_zero, ← map_sub, ← hmem]; exact hIm h
    refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_
    · show resT E.a₁ = E₀.a₁; rw [key _ _ (hqI _ _ d1)]; exact r1
    · show resT E.a₂ = E₀.a₂; rw [key _ _ (hqI _ _ d2)]; exact r2
    · show resT E.a₃ = E₀.a₃; rw [key _ _ (hqI _ _ d3)]; exact r3
    · show resT E.a₄ = E₀.a₄; rw [key _ _ (hqI _ _ d4)]; exact r4
    · show resT E.a₆ = E₀.a₆; rw [key _ _ (hqI _ _ d6)]; exact r6
  have hEΔ : IsUnit E.Δ := by
    by_contra hu
    have hm : E.Δ ∈ maximalIdeal T := (IsLocalRing.mem_maximalIdeal _).mpr hu
    rw [hmem, ← WeierstrassCurve.map_Δ, hEres] at hm
    exact E₀.isUnit_Δ.ne_zero hm
  obtain ⟨G', hG'⟩ := L2Aux.exists_law T E hEΔ
  haveI : G'.IsComm := ⟨by rw [hG']; exact WeierstrassCurve.formalGroupLawFixed_comm_of_commRing E⟩
  have hG'bc : G'.IsBaseChange resT E₀.formalGroup := by
    show E₀.formalGroup.toPowerSeries = MvPowerSeries.map resT G'.toPowerSeries
    rw [hG', ← (WeierstrassCurve.formalW_map_and_formalGroupLawFixed_map E resT).2, hEres]; rfl
  have hcq : PowerSeries.coeff q (G'.nthSeries q) = PowerSeries.coeff q (X.nthSeries q) := by
    have := hL1 G₁ G' hG₁ hG'; rw [sub_eq_iff_eq_add] at this; rw [this]; ring
  have hGG' : ∀ n : Fin 2 →₀ ℕ, MvPowerSeries.coeff n G'.toPowerSeries - MvPowerSeries.coeff n X.toPowerSeries ∈ I := by
    intro n
    rw [← hkerI, map_sub, ← MvPowerSeries.coeff_map, ← MvPowerSeries.coeff_map, hXG₁, hG', hG₁,
      ← (WeierstrassCurve.formalW_map_and_formalGroupLawFixed_map E πI).2,
      ← (WeierstrassCurve.formalW_map_and_formalGroupLawFixed_map E₁ πI).2, hEE₁, sub_self]

  obtain ⟨ψ₁, hψ₁⟩ := FormalGroup.exists_lawIso_of_coeff_nthSeries_eq_of_mul_maximalIdeal_eq_bot q k E₀.formalGroup hE₀ T I hI
    hIm resT hresT hkerT G' X hG'bc hGG' hcq
  obtain ⟨κ, hκs, hκ1⟩ := FormalGroup.LawHom.exists_comp_series_eq_subst ψ₁.toLawHom ξ'.toLawHom
  have hκu : IsUnit (PowerSeries.coeff 1 κ.series) := by
    rw [hκ1]; exact IsUnit.mul ξ'.isUnit_coeff_one ψ₁.isUnit_coeff_one
  have hψ₁res : PowerSeries.map resT ψ₁.series = PowerSeries.X := by
    ext m; rw [PowerSeries.coeff_map, PowerSeries.coeff_X]
    have := (hmem _).mp (hIm (hψ₁ m)); rw [map_sub, sub_eq_zero] at this
    rw [this]; split_ifs <;> simp
  refine ⟨E, hEE₁, G', hG', ⟨κ, hκu⟩, fun m => ?_⟩
  show resT (PowerSeries.coeff m κ.series) = _
  have hfin : PowerSeries.map resT κ.series = PowerSeries.X := by
    rw [hκs, show ψ₁.toLawHom.series = ψ₁.series from rfl, show ξ'.toLawHom.series = ξ'.series from rfl, ← em,
      PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' ψ₁.constantCoeff_series)]
    try simp only [em]
    rw [hψ₁res, hξ's, hsres, PowerSeries.X_subst]
  rw [← PowerSeries.coeff_map, hfin, PowerSeries.coeff_X]

end S_WeierstrassCurve_exists_map_mk_eq_and_lawIso_of_lawIso_quotient_of_mul_maximalIdeal_eq_bot_of_prime
end P2MW
export P2MW.S_WeierstrassCurve_exists_map_mk_eq_and_lawIso_of_lawIso_quotient_of_mul_maximalIdeal_eq_bot_of_prime (solution)
