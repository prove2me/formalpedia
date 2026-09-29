-- Prove2me | solution 1 for WeierstrassCurve.exists_variableChange_map_mk_eq_one_and_smul_eq_of_lawIso_of_mul_maximalIdeal_eq_bot_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/67146aac-d715-5a8b-9ea4-2dcacc3fde29

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Theorems.Thm_WeierstrassCurve_exists_coeff_nthSeries_eq_mul_hasseInvariant
import Theorems.Thm_WeierstrassCurve_exists_map_fstHom_eq_and_snd_hasseInvariant_ne_zero
import Theorems.Thm_WeierstrassCurve_exists_forall_coeff_nthSeries_sub_eq_sum_of_mul_maximalIdeal_eq_bot
import Theorems.Thm_FormalGroup_coeff_nthSeries_eq_of_lawIso_of_mul_maximalIdeal_eq_bot
import Theorems.Thm_WeierstrassCurve_eq_zero_of_firstOrderVariableChange_eq_zero
import Theorems.Thm_WeierstrassCurve_hasseInvariant_variableChange
import Theorems.Thm_WeierstrassCurve_formalW_map_and_formalGroupLawFixed_map
import Theorems.Thm_FormalGroup_IsBaseChange_nthSeries_eq_map
import Theorems.Thm_FormalGroup_isDrinfeldBasisAdic_zero_zero_iff
import Theorems.Thm_WeierstrassCurve_exists_variableChange_map_mk_eq_one_and_smul_eq_of_lawIso_of_mul_maximalIdeal_eq_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_variableChange_map_mk_eq_one_and_smul_eq_of_lawIso_of_mul_maximalIdeal_eq_bot_of_prime
p2m_attr_erase "simp" "ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ"

set_option autoImplicit false

open FormalGroup IsLocalRing

namespace DerivAux

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_exists_variableChange_map_mk_eq_one_and_smul_eq_of_lawIso_of_mul_maximalIdeal_eq_bot_of_prime.WeierstrassCurve"

theorem twoTorsionPolynomial_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (W : WeierstrassCurve R) :
    (W.map f).twoTorsionPolynomial = Cubic.map f W.twoTorsionPolynomial := by
  simp only [WeierstrassCurve.twoTorsionPolynomial, Cubic.map, WeierstrassCurve.map_b₂, WeierstrassCurve.map_b₄,
    WeierstrassCurve.map_b₆, map_mul, map_ofNat]

theorem hasseInvariant_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (q : ℕ) (W : WeierstrassCurve R) :
    (W.map f).hasseInvariant q = f (W.hasseInvariant q) := by
  unfold WeierstrassCurve.hasseInvariant
  rw [twoTorsionPolynomial_map, Cubic.map_toPoly, ← Polynomial.map_pow, Polynomial.coeff_map]

theorem legendreCurve_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (t : R) :
    (legendreCurve t).map f = legendreCurve (f t) := by
  simp only [legendreCurve, WeierstrassCurve.map, map_zero, map_neg, map_add, map_one]

theorem snd_hasseInvariant_eq_sum {k : Type} [Field k] (q : ℕ) (E₀ : WeierstrassCurve k) :
    ∃ c : Fin 5 → k, ∀ (K : Type) [CommRing K] [Algebra k K] (δ : Fin 5 → K)
      (E' : WeierstrassCurve (TrivSqZeroExt K K)),
      E'.a₁ = TrivSqZeroExt.inl (algebraMap k K E₀.a₁) + TrivSqZeroExt.inr (δ 0) →
      E'.a₂ = TrivSqZeroExt.inl (algebraMap k K E₀.a₂) + TrivSqZeroExt.inr (δ 1) →
      E'.a₃ = TrivSqZeroExt.inl (algebraMap k K E₀.a₃) + TrivSqZeroExt.inr (δ 2) →
      E'.a₄ = TrivSqZeroExt.inl (algebraMap k K E₀.a₄) + TrivSqZeroExt.inr (δ 3) →
      E'.a₆ = TrivSqZeroExt.inl (algebraMap k K E₀.a₆) + TrivSqZeroExt.inr (δ 4) →
        (E'.hasseInvariant q).snd = ∑ i, algebraMap k K (c i) * δ i := by
  classical
  let U := TrivSqZeroExt k (Fin 5 → k)
  let Eu : WeierstrassCurve U :=
    ⟨TrivSqZeroExt.inl E₀.a₁ + TrivSqZeroExt.inr (Pi.single 0 1),
     TrivSqZeroExt.inl E₀.a₂ + TrivSqZeroExt.inr (Pi.single 1 1),
     TrivSqZeroExt.inl E₀.a₃ + TrivSqZeroExt.inr (Pi.single 2 1),
     TrivSqZeroExt.inl E₀.a₄ + TrivSqZeroExt.inr (Pi.single 3 1),
     TrivSqZeroExt.inl E₀.a₆ + TrivSqZeroExt.inr (Pi.single 4 1)⟩
  refine ⟨(Eu.hasseInvariant q).snd, ?_⟩
  intro K _ _ δ E' h1 h2 h3 h4 h6

  let L : (Fin 5 → k) →ₗ[k] K :=
    { toFun := fun m => ∑ i, algebraMap k K (m i) * δ i
      map_add' := fun m m' => by
        rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _ => ?_
        rw [Pi.add_apply, map_add, add_mul]
      map_smul' := fun r m => by
        rw [RingHom.id_apply, Finset.smul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
        rw [Pi.smul_apply, smul_eq_mul, map_mul, Algebra.smul_def, mul_assoc] }
  have hL : ∀ m, L m = ∑ i, algebraMap k K (m i) * δ i := fun m => rfl
  let g : (Fin 5 → k) →ₗ[k] TrivSqZeroExt K K := (TrivSqZeroExt.inrHom K K).restrictScalars k ∘ₗ L
  have hg : ∀ m, g m = TrivSqZeroExt.inr (L m) := fun m => rfl
  let Φ : U →ₐ[k] TrivSqZeroExt K K := TrivSqZeroExt.lift (Algebra.ofId k (TrivSqZeroExt K K)) g
    (fun x y => by rw [hg, hg, TrivSqZeroExt.inr_mul_inr])
    (fun r x => by
      rw [hg, hg, map_smul, Algebra.ofId_apply, TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.inl_mul_inr,
        Algebra.smul_def, smul_eq_mul])
    (fun r x => by
      rw [hg, hg, op_smul_eq_smul, map_smul, Algebra.ofId_apply, TrivSqZeroExt.algebraMap_eq_inl',
        TrivSqZeroExt.inr_mul_inl, op_smul_eq_smul, Algebra.smul_def, smul_eq_mul])
  have hΦ : ∀ (a : k) (m : Fin 5 → k), Φ (TrivSqZeroExt.inl a + TrivSqZeroExt.inr m) =
      TrivSqZeroExt.inl (algebraMap k K a) + TrivSqZeroExt.inr (L m) := by
    intro a m
    rw [map_add, TrivSqZeroExt.lift_apply_inl, TrivSqZeroExt.lift_apply_inr, Algebra.ofId_apply,
      TrivSqZeroExt.algebraMap_eq_inl', hg]
  have hLs : ∀ i : Fin 5, L (Pi.single i 1) = δ i := by
    intro i
    rw [hL, Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, map_one, one_mul]
    · intro j _ hj; rw [Pi.single_eq_of_ne hj, map_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hmap : Eu.map Φ.toRingHom = E' := by
    refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_
    · show Φ (TrivSqZeroExt.inl E₀.a₁ + TrivSqZeroExt.inr (Pi.single 0 1)) = E'.a₁
      rw [hΦ, hLs, h1]
    · show Φ (TrivSqZeroExt.inl E₀.a₂ + TrivSqZeroExt.inr (Pi.single 1 1)) = E'.a₂
      rw [hΦ, hLs, h2]
    · show Φ (TrivSqZeroExt.inl E₀.a₃ + TrivSqZeroExt.inr (Pi.single 2 1)) = E'.a₃
      rw [hΦ, hLs, h3]
    · show Φ (TrivSqZeroExt.inl E₀.a₄ + TrivSqZeroExt.inr (Pi.single 3 1)) = E'.a₄
      rw [hΦ, hLs, h4]
    · show Φ (TrivSqZeroExt.inl E₀.a₆ + TrivSqZeroExt.inr (Pi.single 4 1)) = E'.a₆
      rw [hΦ, hLs, h6]
  rw [← hmap, hasseInvariant_map]
  show (Φ (Eu.hasseInvariant q)).snd = _
  conv_lhs => rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq (Eu.hasseInvariant q)]
  rw [hΦ, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, _root_.zero_add, hL]

end DerivAux

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

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map_b₄ isUnit_Δ VariableChange.ext a₃ map_map a₁ map map_b₂ b₂ twoTorsionPolynomial variableChange_a₃ mk a₄ a₂ a₆ variableChange_a₆ variableChange_Δ variableChange_a₂ map_id map_b₆ map_Δ b₆ b₈ variableChange_a₁ variableChange_a₄ Δ VariableChange map_variableChange j b₄ coeff_formalW_three fgSlope fgNu fgZ3Denom fgInv coeff_fgSlope degree_fin2 coeff_one_fgInv two_le_order_fgSlope fgZ3NumFixed fgZ3Fixed formalGroupLawFixed two_le_order_fgZ3NumFixed constantCoeff_fgZ3Fixed hasSubst_fgZ3Fixed constantCoeff_formalGroupLawFixed coeff_zero_formalGroupLawFixed coeff_one_formalGroupLawFixed coeff_two_fgInv three_le_order_fgNu eq_zero_of_degree_lt_one coeff_pow_lt coeff_sq_formalGroupLawFixed formalGroup hasseInvariant legendreCurve exists_forall_coeff_nthSeries_sub_eq_sum_of_mul_maximalIdeal_eq_bot eq_zero_of_firstOrderVariableChange_eq_zero formalW_map_and_formalGroupLawFixed_map exists_variableChange_map_mk_eq_one_and_smul_eq_of_lawIso_of_mul_maximalIdeal_eq_bot"
p2m_open "WeierstrassCurve"
namespace M5HD2

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

noncomputable abbrev d11 : Fin 2 →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 1 1

theorem degree_d11 : Finsupp.degree (d11) = 2 := by
  rw [WeierstrassCurve.degree_fin2]; simp [d11, Finsupp.add_apply]

theorem d11_ne_single_two (i : Fin 2) : (d11 : Fin 2 →₀ ℕ) ≠ Finsupp.single i 2 := by
  intro h
  have hc := congrFun (congrArg DFunLike.coe h) i
  fin_cases i <;> simp [d11, Finsupp.add_apply] at hc

theorem coeff_d11_of_three_le_order (P : MvPowerSeries (Fin 2) R) (hP : (3 : ℕ∞) ≤ P.order) :
    MvPowerSeries.coeff d11 P = 0 := by
  apply MvPowerSeries.coeff_of_lt_order
  calc ((Finsupp.degree (d11 : Fin 2 →₀ ℕ) : ℕ) : ℕ∞) = 2 := by rw [degree_d11]; rfl
    _ < 3 := by norm_num
    _ ≤ P.order := hP

theorem coeff_d11_mul_invD {Num : MvPowerSeries (Fin 2) R} (hNum : (2 : ℕ∞) ≤ Num.order) :
    MvPowerSeries.coeff d11 (Num * MvPowerSeries.invOfUnit W.fgZ3Denom 1)
      = MvPowerSeries.coeff d11 Num := by
  set D := MvPowerSeries.invOfUnit W.fgZ3Denom (1 : Rˣ) with hDdef
  have hD0 : MvPowerSeries.constantCoeff (σ := Fin 2) D = 1 := by
    rw [hDdef, MvPowerSeries.constantCoeff_invOfUnit]; simp
  have hDm1 : (1 : ℕ∞) ≤ (D - 1).order := by
    apply MvPowerSeries.le_order
    intro e he
    rw [WeierstrassCurve.eq_zero_of_degree_lt_one e he, MvPowerSeries.coeff_zero_eq_constantCoeff,
        map_sub, hD0, map_one, sub_self]
  have hcross : MvPowerSeries.coeff d11 (Num * (D - 1)) = 0 := by
    apply coeff_d11_of_three_le_order
    calc (3 : ℕ∞) ≤ 2 + 1 := by norm_num
      _ ≤ Num.order + (D - 1).order := add_le_add hNum hDm1
      _ ≤ _ := MvPowerSeries.le_order_mul
  have hsplit : Num * D = Num + Num * (D - 1) := by ring
  rw [hsplit, map_add, hcross, _root_.add_zero]

theorem coeff_d11_fgZ3NumFixed : MvPowerSeries.coeff d11 W.fgZ3NumFixed = - W.a₁ := by
  have oS := W.two_le_order_fgSlope
  have oN := W.three_le_order_fgNu
  have hsl : MvPowerSeries.coeff d11 W.fgSlope = 1 := by
    rw [W.coeff_fgSlope]
    have h3 : (d11 : Fin 2 →₀ ℕ) 0 + (d11 : Fin 2 →₀ ℕ) 1 + 1 = 3 := by simp [d11, Finsupp.add_apply]
    rw [h3]; exact W.coeff_formalW_three
  have hsl2 : (3 : ℕ∞) ≤ (W.fgSlope ^ 2).order := by
    rw [pow_two]
    exact le_trans (by calc (3 : ℕ∞) ≤ 2 + 2 := by norm_num
                          _ ≤ W.fgSlope.order + W.fgSlope.order := add_le_add oS oS)
      MvPowerSeries.le_order_mul
  have hslN : (3 : ℕ∞) ≤ (W.fgSlope * W.fgNu).order :=
    le_trans (by calc (3 : ℕ∞) ≤ 2 + 3 := by norm_num
                      _ ≤ W.fgSlope.order + W.fgNu.order := add_le_add oS oN)
      MvPowerSeries.le_order_mul
  have hsl2N : (3 : ℕ∞) ≤ (W.fgSlope ^ 2 * W.fgNu).order :=
    le_trans (by calc (3 : ℕ∞) ≤ 3 + 3 := by norm_num
                      _ ≤ (W.fgSlope ^ 2).order + W.fgNu.order := add_le_add hsl2 oN)
      MvPowerSeries.le_order_mul
  unfold fgZ3NumFixed
  rw [map_neg, map_add, map_add, map_add, map_add,
      MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul,
      MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul,
      hsl, coeff_d11_of_three_le_order _ hsl2, coeff_d11_of_three_le_order _ oN,
      coeff_d11_of_three_le_order _ hslN, coeff_d11_of_three_le_order _ hsl2N]
  ring

theorem coeff_d11_fgZ3Fixed : MvPowerSeries.coeff d11 W.fgZ3Fixed = - W.a₁ := by
  have hlin : MvPowerSeries.coeff d11
      ((- MvPowerSeries.X (0 : Fin 2) - MvPowerSeries.X (1 : Fin 2)) : MvPowerSeries (Fin 2) R) = 0 := by
    rw [map_sub, map_neg, MvPowerSeries.coeff_X, MvPowerSeries.coeff_X, if_neg, if_neg]
    · simp
    · intro h; have hc := congrFun (congrArg DFunLike.coe h) 0; simp [d11, Finsupp.add_apply] at hc
    · intro h; have hc := congrFun (congrArg DFunLike.coe h) 1; simp [d11, Finsupp.add_apply] at hc
  unfold fgZ3Fixed
  rw [map_add, hlin, _root_.zero_add, coeff_d11_mul_invD W W.two_le_order_fgZ3NumFixed, coeff_d11_fgZ3NumFixed]

theorem coeff_d11_pow2 {H : MvPowerSeries (Fin 2) R} (hH : (2 : ℕ∞) ≤ H.order) :
    MvPowerSeries.coeff d11 ((- MvPowerSeries.X (0 : Fin 2) - MvPowerSeries.X (1 : Fin 2) + H) ^ 2) = 2 := by
  have hXX1 : (1 : ℕ∞) ≤ (((- MvPowerSeries.X (0 : Fin 2) - MvPowerSeries.X (1 : Fin 2))
      : MvPowerSeries (Fin 2) R)).order := by
    apply MvPowerSeries.le_order
    intro e he
    rw [WeierstrassCurve.eq_zero_of_degree_lt_one e he, MvPowerSeries.coeff_zero_eq_constantCoeff]
    simp [map_sub, map_neg, MvPowerSeries.constantCoeff_X]
  have expand : (- MvPowerSeries.X (0 : Fin 2) - MvPowerSeries.X (1 : Fin 2) + H) ^ 2
      = (MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X 1) ^ 2
        + ((- MvPowerSeries.X (0 : Fin 2) - MvPowerSeries.X (1 : Fin 2)) * H * 2 + H * H) := by ring
  have hcr : MvPowerSeries.coeff d11
      (((- MvPowerSeries.X (0 : Fin 2) - MvPowerSeries.X (1 : Fin 2)) * H * 2 + H * H) : MvPowerSeries (Fin 2) R) = 0 := by
    have hHH : (3 : ℕ∞) ≤ (H * H).order :=
      le_trans (by calc (3 : ℕ∞) ≤ 2 + 2 := by norm_num
                        _ ≤ H.order + H.order := add_le_add hH hH) MvPowerSeries.le_order_mul
    have hLH : (3 : ℕ∞) ≤ ((- MvPowerSeries.X (0 : Fin 2) - MvPowerSeries.X (1 : Fin 2)) * H * 2).order := by
      have hbase : (3 : ℕ∞) ≤ ((- MvPowerSeries.X (0 : Fin 2) - MvPowerSeries.X (1 : Fin 2)) * H).order :=
        le_trans (by calc (3 : ℕ∞) ≤ 1 + 2 := by norm_num
                          _ ≤ (((- MvPowerSeries.X (0 : Fin 2) - MvPowerSeries.X (1 : Fin 2))
                                : MvPowerSeries (Fin 2) R)).order + H.order :=
                            add_le_add hXX1 hH) MvPowerSeries.le_order_mul
      exact le_trans hbase (le_trans le_self_add MvPowerSeries.le_order_mul)
    rw [map_add, coeff_d11_of_three_le_order _ hLH, coeff_d11_of_three_le_order _ hHH, _root_.add_zero]
  rw [expand, map_add, hcr, _root_.add_zero]
  have hexp2 : (MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R) ^ 2
      = MvPowerSeries.X 0 ^ 2 + MvPowerSeries.X 0 * MvPowerSeries.X 1 * 2 + MvPowerSeries.X 1 ^ 2 := by ring
  have hmono : (MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R)
      = MvPowerSeries.monomial (Finsupp.single 0 1 + Finsupp.single 1 1) 1 := by
    rw [MvPowerSeries.X_def, MvPowerSeries.X_def, MvPowerSeries.monomial_mul_monomial, mul_one]
  have hX0X1c : MvPowerSeries.coeff d11
      (MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) = 1 := by
    rw [hmono, MvPowerSeries.coeff_monomial, if_pos rfl]
  have hX0X1 : MvPowerSeries.coeff d11
      (MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X 1 * 2 : MvPowerSeries (Fin 2) R) = 2 := by
    rw [show (MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X 1 * 2 : MvPowerSeries (Fin 2) R)
          = MvPowerSeries.C 2 * (MvPowerSeries.X 0 * MvPowerSeries.X 1) by rw [map_ofNat]; ring,
        MvPowerSeries.coeff_C_mul, hX0X1c, mul_one]
  have hsq : ∀ i : Fin 2, MvPowerSeries.coeff d11 (MvPowerSeries.X i ^ 2 : MvPowerSeries (Fin 2) R) = 0 := by
    intro i
    rw [MvPowerSeries.coeff_X_pow, if_neg (d11_ne_single_two i)]
  rw [hexp2, map_add, map_add, hX0X1, hsq 0, hsq 1]
  ring

theorem coeff_d11_subst {g : MvPowerSeries (Fin 2) R} (hg : PowerSeries.HasSubst g)
    (hgc : MvPowerSeries.constantCoeff (σ := Fin 2) g = 0)
    (hg2 : MvPowerSeries.coeff d11 (g ^ 2) = 2) :
    MvPowerSeries.coeff d11 (PowerSeries.subst g W.fgInv)
      = - MvPowerSeries.coeff d11 g - 2 * W.a₁ := by
  rw [PowerSeries.coeff_subst hg,
    finsum_eq_finsetSum_of_support_subset _ (s := {1, 2}) (by
      intro n hn
      rw [Function.mem_support] at hn
      match n with
      | 0 => exact absurd (by
          rw [pow_zero, MvPowerSeries.coeff_one, if_neg (by
            intro h; have hc := congrFun (congrArg DFunLike.coe h) 0; simp [d11, Finsupp.add_apply] at hc),
              smul_zero]) hn
      | 1 => simp
      | 2 => simp
      | (k + 3) => exact absurd (by
          rw [WeierstrassCurve.coeff_pow_lt hgc d11 (by rw [degree_d11]; omega), smul_zero]) hn),
    Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2), pow_one, W.coeff_one_fgInv, W.coeff_two_fgInv, hg2]
  simp only [smul_eq_mul]
  ring

theorem coeff_d11_formalGroupLawFixed :
    MvPowerSeries.coeff d11 W.formalGroupLawFixed = - W.a₁ := by
  have hpow2 : MvPowerSeries.coeff d11 (W.fgZ3Fixed ^ 2) = 2 := by
    have hH : (2 : ℕ∞) ≤ (W.fgZ3NumFixed * MvPowerSeries.invOfUnit W.fgZ3Denom 1).order :=
      le_trans W.two_le_order_fgZ3NumFixed (le_trans le_self_add MvPowerSeries.le_order_mul)
    have := coeff_d11_pow2 (R := R) hH
    rwa [show (- MvPowerSeries.X (0 : Fin 2) - MvPowerSeries.X (1 : Fin 2)
      + W.fgZ3NumFixed * MvPowerSeries.invOfUnit W.fgZ3Denom 1) = W.fgZ3Fixed from rfl] at this
  unfold formalGroupLawFixed
  rw [coeff_d11_subst W W.hasSubst_fgZ3Fixed W.constantCoeff_fgZ3Fixed hpow2, coeff_d11_fgZ3Fixed]
  ring

end M5HD2
end WeierstrassCurve

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map_b₄ isUnit_Δ VariableChange.ext a₃ map_map a₁ map map_b₂ b₂ twoTorsionPolynomial variableChange_a₃ mk a₄ a₂ a₆ variableChange_a₆ variableChange_Δ variableChange_a₂ map_id map_b₆ map_Δ b₆ b₈ variableChange_a₁ variableChange_a₄ Δ VariableChange map_variableChange j b₄ coeff_formalW_three fgSlope fgNu fgZ3Denom fgInv coeff_fgSlope degree_fin2 coeff_one_fgInv two_le_order_fgSlope fgZ3NumFixed fgZ3Fixed formalGroupLawFixed two_le_order_fgZ3NumFixed constantCoeff_fgZ3Fixed hasSubst_fgZ3Fixed constantCoeff_formalGroupLawFixed coeff_zero_formalGroupLawFixed coeff_one_formalGroupLawFixed coeff_two_fgInv three_le_order_fgNu eq_zero_of_degree_lt_one coeff_pow_lt coeff_sq_formalGroupLawFixed formalGroup hasseInvariant legendreCurve exists_forall_coeff_nthSeries_sub_eq_sum_of_mul_maximalIdeal_eq_bot eq_zero_of_firstOrderVariableChange_eq_zero formalW_map_and_formalGroupLawFixed_map exists_variableChange_map_mk_eq_one_and_smul_eq_of_lawIso_of_mul_maximalIdeal_eq_bot"
p2m_open "WeierstrassCurve"
namespace M5HD2

open MvPowerSeries in
theorem coeff_subst_eq_zero_of_lowdeg {R : Type*} [CommRing R] {τ : Type*}
    (a : Fin 2 → MvPowerSeries τ R) (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    (Rm : MvPowerSeries (Fin 2) R) (n : ℕ) (hRm : ∀ d : Fin 2 →₀ ℕ, Finsupp.degree d ≤ n → MvPowerSeries.coeff d Rm = 0)
    (e : τ →₀ ℕ) (he : Finsupp.degree e ≤ n) :
    MvPowerSeries.coeff e (MvPowerSeries.subst a Rm) = 0 := by
  have hsub : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  rw [MvPowerSeries.coeff_subst hsub]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  by_cases hd : Finsupp.degree d ≤ n
  · rw [hRm d hd]; simp
  · have hd' : n < Finsupp.degree d := not_le.mp hd
    have h1 : ∀ s, (1 : ℕ∞) ≤ (a s).order := by
      intro s
      apply MvPowerSeries.le_order
      intro e' he'
      have hdeg : Finsupp.degree e' = 0 := by
        have : (Finsupp.degree e' : ℕ) < 1 := by exact_mod_cast he'
        omega
      have : e' = 0 := (Finsupp.degree_eq_zero_iff _).mp hdeg
      rw [this, MvPowerSeries.coeff_zero_eq_constantCoeff, ha]
    have hprod : ((Finsupp.degree d : ℕ) : ℕ∞) ≤ (d.prod fun s m => a s ^ m).order := by
      rw [Finsupp.prod_fintype _ _ (fun i => by simp), Fin.prod_univ_two, WeierstrassCurve.degree_fin2]
      have hp : ∀ s, ((d s : ℕ) : ℕ∞) ≤ (a s ^ d s).order := by
        intro s
        calc ((d s : ℕ) : ℕ∞) = (d s) • (1 : ℕ∞) := by simp
          _ ≤ (d s) • (a s).order := nsmul_le_nsmul_right (h1 s) _
          _ ≤ (a s ^ d s).order := MvPowerSeries.le_order_pow _
      calc (((d 0 + d 1 : ℕ)) : ℕ∞) = ((d 0 : ℕ) : ℕ∞) + ((d 1 : ℕ) : ℕ∞) := by push_cast; rfl
        _ ≤ (a 0 ^ d 0).order + (a 1 ^ d 1).order := add_le_add (hp 0) (hp 1)
        _ ≤ _ := MvPowerSeries.le_order_mul
    have hz : MvPowerSeries.coeff e (d.prod fun s m => a s ^ m) = 0 := by
      apply MvPowerSeries.coeff_of_lt_order
      calc ((Finsupp.degree e : ℕ) : ℕ∞) ≤ n := by exact_mod_cast he
        _ < ((Finsupp.degree d : ℕ) : ℕ∞) := by exact_mod_cast hd'
        _ ≤ _ := hprod
    rw [hz]; simp

noncomputable def quad {R : Type*} [CommRing R] (W : WeierstrassCurve R) : MvPowerSeries (Fin 2) R :=
  MvPowerSeries.X 0 + MvPowerSeries.X 1 + (- W.a₁) • (MvPowerSeries.X 0 * MvPowerSeries.X 1)

theorem X0_mul_X1_eq_monomial {R : Type*} [CommRing R] :
    (MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R)
      = MvPowerSeries.monomial (Finsupp.single 0 1 + Finsupp.single 1 1) 1 := by
  rw [MvPowerSeries.X_def, MvPowerSeries.X_def, MvPowerSeries.monomial_mul_monomial, mul_one]

theorem coeff_quad {R : Type*} [CommRing R] (W : WeierstrassCurve R) (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d (quad W)
      = (if d = Finsupp.single 0 1 then 1 else 0) + (if d = Finsupp.single 1 1 then 1 else 0)
        + (- W.a₁) * (if d = d11 then 1 else 0) := by
  unfold quad
  rw [map_add, map_add, MvPowerSeries.coeff_X, MvPowerSeries.coeff_X, map_smul,
    X0_mul_X1_eq_monomial, MvPowerSeries.coeff_monomial, smul_eq_mul]

theorem single_ne_d11 (s : Fin 2) (c : ℕ) : (Finsupp.single s c : Fin 2 →₀ ℕ) ≠ d11 := by
  intro h
  fin_cases s
  · have hc := congrFun (congrArg DFunLike.coe h) 1; simp [d11, Finsupp.add_apply] at hc
  · have hc := congrFun (congrArg DFunLike.coe h) 0; simp [d11, Finsupp.add_apply] at hc

theorem d11_ne_single (s : Fin 2) (c : ℕ) : (d11 : Fin 2 →₀ ℕ) ≠ Finsupp.single s c := fun h => single_ne_d11 s c h.symm

theorem zero_ne_d11 : (0 : Fin 2 →₀ ℕ) ≠ d11 := by
  intro h; have hc := congrFun (congrArg DFunLike.coe h) 0; simp [d11, Finsupp.add_apply] at hc

theorem zero_eq_single_iff (s : Fin 2) (c : ℕ) : ((0 : Fin 2 →₀ ℕ) = Finsupp.single s c) ↔ c = 0 := by
  rw [eq_comm, Finsupp.single_eq_zero]

theorem coeff_remainder_eq_zero {R : Type*} [CommRing R] (W : WeierstrassCurve R)
    (d : Fin 2 →₀ ℕ) (hd : Finsupp.degree d ≤ 2) :
    MvPowerSeries.coeff d (W.formalGroupLawFixed - (quad W)) = 0 := by
  rw [map_sub, coeff_quad, sub_eq_zero]
  rw [WeierstrassCurve.degree_fin2] at hd
  obtain ⟨i, hi⟩ : ∃ i, d 0 = i := ⟨_, rfl⟩
  obtain ⟨j, hj⟩ : ∃ j, d 1 = j := ⟨_, rfl⟩
  have hij : i + j ≤ 2 := by omega
  have hdij : d = Finsupp.single 0 i + Finsupp.single 1 j := by
    ext s; fin_cases s <;> simp [Finsupp.add_apply, hi, hj]
  subst hdij
  have hi2 : i ≤ 2 := by omega
  have hj2 : j ≤ 2 := by omega

  have E : ∀ (a b c e : ℕ), ((Finsupp.single (0:Fin 2) a + Finsupp.single (1:Fin 2) b : Fin 2 →₀ ℕ)
      = Finsupp.single 0 c + Finsupp.single 1 e) ↔ (a = c ∧ b = e) := by
    intro a b c e
    constructor
    · intro h
      have h0 := congrFun (congrArg DFunLike.coe h) 0
      have h1 := congrFun (congrArg DFunLike.coe h) 1
      simp [Finsupp.add_apply] at h0 h1
      exact ⟨h0, h1⟩
    · rintro ⟨rfl, rfl⟩; rfl
  have S0 : ∀ c : ℕ, (Finsupp.single (0:Fin 2) c : Fin 2 →₀ ℕ) = Finsupp.single 0 c + Finsupp.single 1 0 := by
    intro c; simp
  have S1 : ∀ c : ℕ, (Finsupp.single (1:Fin 2) c : Fin 2 →₀ ℕ) = Finsupp.single 0 0 + Finsupp.single 1 c := by
    intro c; simp
  have D11 : (d11 : Fin 2 →₀ ℕ) = Finsupp.single 0 1 + Finsupp.single 1 1 := rfl
  interval_cases i <;> interval_cases j
  all_goals (first | (exfalso; omega) | skip)
  ·
    have h := W.constantCoeff_formalGroupLawFixed
    have hz : (Finsupp.single (0:Fin 2) 0 + Finsupp.single (1:Fin 2) 0 : Fin 2 →₀ ℕ) = 0 := by simp
    rw [hz, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h]
    simp [Finsupp.single_eq_single_iff, single_ne_d11, d11_ne_single, zero_ne_d11, zero_eq_single_iff]
  ·
    rw [show (Finsupp.single (0:Fin 2) 0 + Finsupp.single (1:Fin 2) 1 : Fin 2 →₀ ℕ) = Finsupp.single 1 1 by simp,
      W.coeff_one_formalGroupLawFixed]
    simp [Finsupp.single_eq_single_iff, single_ne_d11, d11_ne_single, zero_ne_d11, zero_eq_single_iff]
  ·
    rw [show (Finsupp.single (0:Fin 2) 0 + Finsupp.single (1:Fin 2) 2 : Fin 2 →₀ ℕ) = Finsupp.single 1 2 by simp,
      W.coeff_sq_formalGroupLawFixed 1]
    simp [Finsupp.single_eq_single_iff, single_ne_d11, d11_ne_single, zero_ne_d11, zero_eq_single_iff]
  ·
    rw [show (Finsupp.single (0:Fin 2) 1 + Finsupp.single (1:Fin 2) 0 : Fin 2 →₀ ℕ) = Finsupp.single 0 1 by simp,
      W.coeff_zero_formalGroupLawFixed]
    simp [Finsupp.single_eq_single_iff, single_ne_d11, d11_ne_single, zero_ne_d11, zero_eq_single_iff]
  ·
    rw [show (Finsupp.single (0:Fin 2) 1 + Finsupp.single (1:Fin 2) 1 : Fin 2 →₀ ℕ) = d11 from rfl, coeff_d11_formalGroupLawFixed]
    simp [Finsupp.single_eq_single_iff, single_ne_d11, d11_ne_single, zero_ne_d11, zero_eq_single_iff]
  ·
    rw [show (Finsupp.single (0:Fin 2) 2 + Finsupp.single (1:Fin 2) 0 : Fin 2 →₀ ℕ) = Finsupp.single 0 2 by simp,
      W.coeff_sq_formalGroupLawFixed 0]
    simp [Finsupp.single_eq_single_iff, single_ne_d11, d11_ne_single, zero_ne_d11, zero_eq_single_iff]

end M5HD2
end WeierstrassCurve

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map_b₄ isUnit_Δ VariableChange.ext a₃ map_map a₁ map map_b₂ b₂ twoTorsionPolynomial variableChange_a₃ mk a₄ a₂ a₆ variableChange_a₆ variableChange_Δ variableChange_a₂ map_id map_b₆ map_Δ b₆ b₈ variableChange_a₁ variableChange_a₄ Δ VariableChange map_variableChange j b₄ coeff_formalW_three fgSlope fgNu fgZ3Denom fgInv coeff_fgSlope degree_fin2 coeff_one_fgInv two_le_order_fgSlope fgZ3NumFixed fgZ3Fixed formalGroupLawFixed two_le_order_fgZ3NumFixed constantCoeff_fgZ3Fixed hasSubst_fgZ3Fixed constantCoeff_formalGroupLawFixed coeff_zero_formalGroupLawFixed coeff_one_formalGroupLawFixed coeff_two_fgInv three_le_order_fgNu eq_zero_of_degree_lt_one coeff_pow_lt coeff_sq_formalGroupLawFixed formalGroup hasseInvariant legendreCurve exists_forall_coeff_nthSeries_sub_eq_sum_of_mul_maximalIdeal_eq_bot eq_zero_of_firstOrderVariableChange_eq_zero formalW_map_and_formalGroupLawFixed_map exists_variableChange_map_mk_eq_one_and_smul_eq_of_lawIso_of_mul_maximalIdeal_eq_bot"
p2m_open "WeierstrassCurve"
namespace M5HD2

theorem psCoeff_eq {R : Type*} [CommRing R] (n : ℕ) (f : PowerSeries R) :
    PowerSeries.coeff n f = MvPowerSeries.coeff (Finsupp.single () n) f := by
  rw [PowerSeries.coeff_def (s := Finsupp.single () n) (Finsupp.single_eq_same)]

theorem subst_quad {R : Type*} [CommRing R] (W : WeierstrassCurve R) (a : Fin 2 → PowerSeries R)
    (ha : MvPowerSeries.HasSubst a) :
    MvPowerSeries.subst a (quad W) = a 0 + a 1 + (- W.a₁) • (a 0 * a 1) := by
  unfold quad
  rw [MvPowerSeries.subst_add ha, MvPowerSeries.subst_add ha, MvPowerSeries.subst_X ha, MvPowerSeries.subst_X ha,
      MvPowerSeries.subst_smul ha, MvPowerSeries.subst_mul ha, MvPowerSeries.subst_X ha, MvPowerSeries.subst_X ha]

theorem coeff_two_nthSeries_two {R : Type*} [CommRing R] (W : WeierstrassCurve R)
    (G : FormalGroup R) (hG : G.toPowerSeries = W.formalGroupLawFixed) :
    PowerSeries.coeff 2 (G.nthSeries 2) = - W.a₁ := by
  set Rm := W.formalGroupLawFixed - quad W with hRm
  have hF : G.toPowerSeries = quad W + Rm := by rw [hG, hRm]; abel
  have hRm0 : ∀ d : Fin 2 →₀ ℕ, Finsupp.degree d ≤ 2 → MvPowerSeries.coeff d Rm = 0 :=
    fun d hd => by rw [hRm]; exact coeff_remainder_eq_zero W d hd

  have ha1 : ∀ s, MvPowerSeries.constantCoeff ((![0, PowerSeries.X] : Fin 2 → PowerSeries R) s) = 0 := by
    intro s; fin_cases s
    · simp
    · simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one]
      exact PowerSeries.constantCoeff_X
  have hs1 : MvPowerSeries.HasSubst (![0, PowerSeries.X] : Fin 2 → PowerSeries R) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero ha1
  have hu_eq : G.nthSeries 1 = PowerSeries.X + MvPowerSeries.subst ![0, PowerSeries.X] Rm := by
    rw [FormalGroup.nthSeries_succ, FormalGroup.nthSeries_zero, hF, MvPowerSeries.subst_add hs1, subst_quad W _ hs1]
    simp
  have hu0 : PowerSeries.constantCoeff (G.nthSeries 1) = 0 := G.constantCoeff_nthSeries 1
  have hu1 : PowerSeries.coeff 1 (G.nthSeries 1) = 1 := by
    rw [hu_eq, map_add, PowerSeries.coeff_one_X, psCoeff_eq,
      coeff_subst_eq_zero_of_lowdeg _ ha1 Rm 2 hRm0 _ (by rw [Finsupp.degree_single]; norm_num), _root_.add_zero]
  have hu2 : PowerSeries.coeff 2 (G.nthSeries 1) = 0 := by
    rw [hu_eq, map_add, PowerSeries.coeff_X, if_neg (by norm_num), psCoeff_eq,
      coeff_subst_eq_zero_of_lowdeg _ ha1 Rm 2 hRm0 _ (by rw [Finsupp.degree_single]), _root_.add_zero]

  have ha2 : ∀ s, MvPowerSeries.constantCoeff ((![G.nthSeries 1, PowerSeries.X] : Fin 2 → PowerSeries R) s) = 0 := by
    intro s; fin_cases s
    · first | simpa using hu0 | exact hu0
    · simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one]
      exact PowerSeries.constantCoeff_X
  have hs2 : MvPowerSeries.HasSubst (![G.nthSeries 1, PowerSeries.X] : Fin 2 → PowerSeries R) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero ha2
  rw [show G.nthSeries 2 = MvPowerSeries.subst ![G.nthSeries 1, PowerSeries.X] G.toPowerSeries from
    FormalGroup.nthSeries_succ G 1, hF, MvPowerSeries.subst_add hs2, subst_quad W _ hs2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [map_add, map_add, map_add, map_smul, hu2, PowerSeries.coeff_X, if_neg (by norm_num),
    show (2 : ℕ) = 1 + 1 from rfl, PowerSeries.coeff_succ_mul_X, hu1, psCoeff_eq (1 + 1),
    coeff_subst_eq_zero_of_lowdeg _ ha2 Rm 2 hRm0 _ (by rw [Finsupp.degree_single])]
  simp

theorem hasseDeriv_two (k : Type) [Field k] (E₀ : WeierstrassCurve k) :
    ∃ E₁ : WeierstrassCurve (DualNumber k),
      E₁.map (TrivSqZeroExt.fstHom k k k).toRingHom = E₀ ∧
      ∀ G : FormalGroup (DualNumber k), G.toPowerSeries = E₁.formalGroupLawFixed →
        TrivSqZeroExt.snd (PowerSeries.coeff 2 (G.nthSeries 2)) ≠ 0 := by
  refine ⟨⟨TrivSqZeroExt.inl E₀.a₁ + DualNumber.eps, TrivSqZeroExt.inl E₀.a₂, TrivSqZeroExt.inl E₀.a₃,
    TrivSqZeroExt.inl E₀.a₄, TrivSqZeroExt.inl E₀.a₆⟩, ?_, ?_⟩
  · ext <;> simp [WeierstrassCurve.map]
  · intro G hG
    rw [coeff_two_nthSeries_two _ G hG]
    simp

end M5HD2
end WeierstrassCurve

theorem solution
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
    (E₀ : WeierstrassCurve k) [E₀.IsElliptic] (hE₀ : E₀.formalGroup.IsDrinfeldBasisAdic ⊥ q 0 0)
    (T : Type) [CommRing T] [IsLocalRing T] (I : Ideal T) (hI : I * maximalIdeal T = ⊥) (hIm : I ≤ maximalIdeal T)
    (resT : T →+* k) (hresT : Function.Surjective resT) (hkerT : RingHom.ker resT = maximalIdeal T)
    (E E' : WeierstrassCurve T) (hE : E.map resT = E₀)
    (hEE' : E'.map (Ideal.Quotient.mk I) = E.map (Ideal.Quotient.mk I))
    (G : FormalGroup T) (hG : G.toPowerSeries = E.formalGroupLawFixed)
    (G' : FormalGroup T) (hG' : G'.toPowerSeries = E'.formalGroupLawFixed)
    (ψ : FormalGroup.LawIso G G')
    (hψ : ∀ m : ℕ, PowerSeries.coeff m ψ.series - (if m = 1 then 1 else 0) ∈ I) :
    ∃ C : WeierstrassCurve.VariableChange T, C.map (Ideal.Quotient.mk I) = 1 ∧ C • E = E' := by
  by_cases hq : q ≠ 2
  · exact WeierstrassCurve.exists_variableChange_map_mk_eq_one_and_smul_eq_of_lawIso_of_mul_maximalIdeal_eq_bot q hq k E₀ hE₀ T I hI hIm resT hresT hkerT E E' hE hEE' G hG G' hG' ψ hψ
  have hq2' : q = 2 := not_not.mp hq
  classical
  have hprime : q.Prime := Fact.out
  have hq2 : 2 ≤ q := hprime.two_le
  have hqlt : q < q * q := by nlinarith
  have hmem : ∀ x : T, x ∈ maximalIdeal T ↔ resT x = 0 := fun x => by rw [← hkerT, RingHom.mem_ker]
  have hImul : ∀ a b : T, a ∈ I → b ∈ maximalIdeal T → a * b = 0 := by
    intro a b ha hb
    have : a * b ∈ I * maximalIdeal T := Ideal.mul_mem_mul ha hb
    rwa [hI, Ideal.mem_bot] at this

  set π : DualNumber k →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom with hπ
  have hπapp : ∀ x : DualNumber k, π x = TrivSqZeroExt.fst x := fun x => by rw [hπ]; rfl
  have hinl : ∀ x : k, algebraMap k (DualNumber k) x = TrivSqZeroExt.inl x :=
    fun x => congrFun (TrivSqZeroExt.algebraMap_eq_inl k k) x
  have hres : ∀ a : k, π (algebraMap k (DualNumber k) a) = a := fun a => by
    rw [hπapp, hinl]; exact TrivSqZeroExt.fst_inl k a
  have hπsurj : Function.Surjective π := fun a => ⟨algebraMap k _ a, hres a⟩
  have hkerε : RingHom.ker π = maximalIdeal (DualNumber k) :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective π hπsurj)
  have hsqε : maximalIdeal (DualNumber k) * maximalIdeal (DualNumber k) = ⊥ := by
    rw [← pow_two, DualNumber.maximalIdeal_eq_span_singleton_eps, Ideal.span_singleton_pow, pow_two,
      DualNumber.eps_mul_eps, Ideal.span_singleton_eq_bot]
  haveI : CharP (DualNumber k) q := charP_of_injective_algebraMap (algebraMap k (DualNumber k)).injective q
  have hπalg : π.comp (algebraMap k (DualNumber k)) = RingHom.id k := RingHom.ext hres
  have hmemε : ∀ x : DualNumber k, x ∈ maximalIdeal (DualNumber k) ↔ TrivSqZeroExt.fst x = 0 := fun x => by
    rw [← hkerε, RingHom.mem_ker, hπapp]

  set Eε : WeierstrassCurve (DualNumber k) := E₀.map (algebraMap k (DualNumber k)) with hEε
  have hEεa : Eε.a₁ = TrivSqZeroExt.inl E₀.a₁ ∧ Eε.a₂ = TrivSqZeroExt.inl E₀.a₂ ∧ Eε.a₃ = TrivSqZeroExt.inl E₀.a₃ ∧
      Eε.a₄ = TrivSqZeroExt.inl E₀.a₄ ∧ Eε.a₆ = TrivSqZeroExt.inl E₀.a₆ := by
    rw [hEε]; exact ⟨hinl _, hinl _, hinl _, hinl _, hinl _⟩
  have hEεπ : Eε.map π = E₀ := by rw [hEε, WeierstrassCurve.map_map, hπalg, WeierstrassCurve.map_id]
  set Gε : FormalGroup (DualNumber k) := E₀.formalGroup.map (algebraMap k (DualNumber k)) with hGε
  have hGεser : Gε.toPowerSeries = Eε.formalGroupLawFixed := by
    rw [hGε, FormalGroup.map_toPowerSeries, hEε,
      (WeierstrassCurve.formalW_map_and_formalGroupLawFixed_map E₀ (algebraMap k (DualNumber k))).2]; rfl

  have hP2 : ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R) (G₁ : FormalGroup R),
      G₁.toPowerSeries = W.formalGroupLawFixed → PowerSeries.coeff q (G₁.nthSeries q) = - W.a₁ := by
    intro R _ W G₁ hG₁; rw [hq2']; exact WeierstrassCurve.M5HD2.coeff_two_nthSeries_two W G₁ hG₁
  haveI : IsAdicComplete (⊥ : Ideal k) k := inferInstance
  obtain ⟨u₀, hu₀, hq0⟩ := (FormalGroup.isDrinfeldBasisAdic_zero_zero_iff (⊥ : Ideal k) E₀.formalGroup q).mp hE₀
  have ha10 : E₀.a₁ = 0 := by
    have h1 := hP2 k E₀ E₀.formalGroup rfl
    rw [hq0, PowerSeries.coeff_mul_X_pow', if_neg (not_le.mpr hqlt)] at h1
    exact neg_eq_zero.mp h1.symm
  have h2ε : (2 : DualNumber k) = 0 := by
    have h := CharP.cast_eq_zero (DualNumber k) q
    rw [hq2'] at h; exact_mod_cast h
  have hcoefε : PowerSeries.coeff q (Gε.nthSeries q) = 0 := by
    rw [hP2 (DualNumber k) Eε Gε hGεser, hEεa.1, ha10, TrivSqZeroExt.inl_zero, neg_zero]

  have hsnd_c : ∀ (a : k) (x : DualNumber k), TrivSqZeroExt.snd ((algebraMap k (DualNumber k) a) * x) =
      a * TrivSqZeroExt.snd x := by
    intro a x
    rw [hinl, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, smul_zero, _root_.add_zero, smul_eq_mul]

  obtain ⟨c, hc⟩ := WeierstrassCurve.exists_forall_coeff_nthSeries_sub_eq_sum_of_mul_maximalIdeal_eq_bot q k E₀

  have hFOε : ∀ (E' : WeierstrassCurve (DualNumber k)) (G' : FormalGroup (DualNumber k)),
      E'.map π = E₀ → G'.toPowerSeries = E'.formalGroupLawFixed →
      TrivSqZeroExt.snd (PowerSeries.coeff q (G'.nthSeries q)) =
        ∑ i, c i * (![E'.a₁.snd, E'.a₂.snd, E'.a₃.snd, E'.a₄.snd, E'.a₆.snd] : Fin 5 → k) i := by
    intro E' G' hE' hG'
    obtain ⟨e1, e2, e3, e4, e6⟩ := WeierstrassCurve.ext_iff.mp hE'
    have key : ∀ (x : DualNumber k) (a : k), π x = a → x - TrivSqZeroExt.inl a ∈ maximalIdeal (DualNumber k) := by
      intro x a hx; rw [hmemε, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_inl, ← hπapp, hx, sub_self]
    have e := hc (DualNumber k) (maximalIdeal (DualNumber k)) hsqε le_rfl π hπsurj hkerε Eε E' hEεπ (by
        obtain ⟨f1, f2, f3, f4, f6⟩ := hEεa
        refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_
        · show Ideal.Quotient.mk _ E'.a₁ = Ideal.Quotient.mk _ Eε.a₁; rw [f1, Ideal.Quotient.eq]; exact key _ _ e1
        · show Ideal.Quotient.mk _ E'.a₂ = Ideal.Quotient.mk _ Eε.a₂; rw [f2, Ideal.Quotient.eq]; exact key _ _ e2
        · show Ideal.Quotient.mk _ E'.a₃ = Ideal.Quotient.mk _ Eε.a₃; rw [f3, Ideal.Quotient.eq]; exact key _ _ e3
        · show Ideal.Quotient.mk _ E'.a₄ = Ideal.Quotient.mk _ Eε.a₄; rw [f4, Ideal.Quotient.eq]; exact key _ _ e4
        · show Ideal.Quotient.mk _ E'.a₆ = Ideal.Quotient.mk _ Eε.a₆; rw [f6, Ideal.Quotient.eq]; exact key _ _ e6)
      Gε G' hGεser hG' (fun i => algebraMap k (DualNumber k) (c i)) (fun i => hres (c i))
    have e' := congrArg TrivSqZeroExt.snd e
    rw [TrivSqZeroExt.snd_sub, hcoefε, TrivSqZeroExt.snd_zero, sub_zero] at e'
    rw [e']
    obtain ⟨f1, f2, f3, f4, f6⟩ := hEεa
    simp only [TrivSqZeroExt.snd_add, hsnd_c, TrivSqZeroExt.snd_sub, f1, f2, f3, f4, f6, TrivSqZeroExt.snd_inl, sub_zero,
      Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    try rfl

  have hcomp : LinearMap.range (H2Aux.tangentMap E₀) ≤ LinearMap.ker (H2Aux.functional c) := by
    rintro _ ⟨m, rfl⟩
    rw [LinearMap.mem_ker, H2Aux.functional_apply]
    set E' := H2Aux.Cinf (m 0) (m 1) (m 2) (m 3) • Eε with hE'
    have hE'π : E'.map π = E₀ := by
      rw [hE', ← WeierstrassCurve.map_variableChange, hEεπ, hπ, H2Aux.Cinf_map_fst, one_smul]
    have hΔ' : IsUnit E'.Δ := by
      rw [hE', WeierstrassCurve.variableChange_Δ]
      refine IsUnit.mul (IsUnit.pow _ (Units.isUnit _)) ?_
      rw [hEε, WeierstrassCurve.map_Δ]; exact E₀.isUnit_Δ.map _
    obtain ⟨G', hG'⟩ := L2Aux.exists_law _ E' hΔ'
    have e := hFOε E' G' hE'π hG'
    have hL0 : PowerSeries.coeff q (G'.nthSeries q) = 0 := by
      rw [hP2 (DualNumber k) E' G' hG', hE', WeierstrassCurve.variableChange_a₁, hEεa.1, ha10, TrivSqZeroExt.inl_zero,
        _root_.zero_add, h2ε, zero_mul, mul_zero, neg_zero]
    rw [hL0, TrivSqZeroExt.snd_zero, hE'] at e
    have hsm := H2Aux.Cinf_smul E₀ (m 0) (m 1) (m 2) (m 3)
    rw [← hEε] at hsm
    rw [hsm] at e
    simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, _root_.zero_add] at e
    rw [e, H2Aux.tangentMap_apply]
    all_goals (simp only [Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; try rfl)

  set E₂ : WeierstrassCurve (DualNumber k) := ⟨TrivSqZeroExt.inl E₀.a₁ + DualNumber.eps, TrivSqZeroExt.inl E₀.a₂,
    TrivSqZeroExt.inl E₀.a₃, TrivSqZeroExt.inl E₀.a₄, TrivSqZeroExt.inl E₀.a₆⟩ with hE₂def
  have hE₂ : E₂.map π = E₀ := by
    rw [hE₂def, hπ]; ext <;> simp [WeierstrassCurve.map]
  have hΔ₂ : IsUnit E₂.Δ := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, ← hπapp, ← WeierstrassCurve.map_Δ, hE₂]; exact E₀.isUnit_Δ
  obtain ⟨G₂, hG₂⟩ := L2Aux.exists_law _ E₂ hΔ₂
  set v₂ : Fin 5 → k := ![E₂.a₁.snd, E₂.a₂.snd, E₂.a₃.snd, E₂.a₄.snd, E₂.a₆.snd] with hv₂
  have hlam₂ : H2Aux.functional c v₂ ≠ 0 := by
    rw [H2Aux.functional_apply, hv₂, ← hFOε E₂ G₂ hE₂ hG₂, hP2 (DualNumber k) E₂ G₂ hG₂, hE₂def]
    simp
  have hkereq : LinearMap.range (H2Aux.tangentMap E₀) = LinearMap.ker (H2Aux.functional c) :=
    H2Aux.range_eq_ker _ (H2Aux.tangentMap_injective E₀) _ hcomp v₂ hlam₂
  set v : Fin 5 → k := (H2Aux.functional c v₂)⁻¹ • v₂ with hv
  have hv1 : H2Aux.functional c v = 1 := by rw [hv, map_smul, smul_eq_mul, inv_mul_cancel₀ hlam₂]
  obtain ⟨g, w, hgw⟩ := L2Aux.exists_leftInverse_defect _ (H2Aux.tangentMap_injective E₀) _ hkereq v hv1

  set δ : Fin 5 → T := ![E'.a₁ - E.a₁, E'.a₂ - E.a₂, E'.a₃ - E.a₃, E'.a₄ - E.a₄, E'.a₆ - E.a₆] with hδ
  obtain ⟨d1, d2, d3, d4, d6⟩ := WeierstrassCurve.ext_iff.mp hEE'
  have hqI : ∀ x y : T, Ideal.Quotient.mk I x = Ideal.Quotient.mk I y → x - y ∈ I := fun x y h => (Ideal.Quotient.eq).mp h
  have hδI : ∀ i, δ i ∈ I := by
    intro i; rw [hδ]; fin_cases i
    · exact hqI _ _ d1
    · exact hqI _ _ d2
    · exact hqI _ _ d3
    · exact hqI _ _ d4
    · exact hqI _ _ d6
  obtain ⟨r1, r2, r3, r4, r6⟩ := WeierstrassCurve.ext_iff.mp hE
  have hE'res : E'.map resT = E₀ := by
    have key : ∀ x y : T, x - y ∈ I → resT x = resT y := by
      intro x y h; rw [← sub_eq_zero, ← map_sub, ← hmem]; exact hIm h
    refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_
    · show resT E'.a₁ = E₀.a₁; rw [key _ _ (hqI _ _ d1)]; exact r1
    · show resT E'.a₂ = E₀.a₂; rw [key _ _ (hqI _ _ d2)]; exact r2
    · show resT E'.a₃ = E₀.a₃; rw [key _ _ (hqI _ _ d3)]; exact r3
    · show resT E'.a₄ = E₀.a₄; rw [key _ _ (hqI _ _ d4)]; exact r4
    · show resT E'.a₆ = E₀.a₆; rw [key _ _ (hqI _ _ d6)]; exact r6
  have hGbc : G.IsBaseChange resT E₀.formalGroup := by
    show E₀.formalGroup.toPowerSeries = MvPowerSeries.map resT G.toPowerSeries
    rw [hG, ← (WeierstrassCurve.formalW_map_and_formalGroupLawFixed_map E resT).2, hE]; rfl
  have hG'bc : G'.IsBaseChange resT E₀.formalGroup := by
    show E₀.formalGroup.toPowerSeries = MvPowerSeries.map resT G'.toPowerSeries
    rw [hG', ← (WeierstrassCurve.formalW_map_and_formalGroupLawFixed_map E' resT).2, hE'res]; rfl
  have hstar := FormalGroup.coeff_nthSeries_eq_of_lawIso_of_mul_maximalIdeal_eq_bot q k E₀.formalGroup hE₀ T I hI resT
    hkerT G G' hGbc hG'bc ψ hψ
  choose t ht using fun i : Fin 5 => hresT (c i)
  have hFO := hc T I hI hIm resT hresT hkerT E E' hE hEE' G G' hG hG' t ht
  rw [hstar, sub_self] at hFO
  have hsum : ∑ i, t i * δ i = 0 := by
    rw [hδ, Fin.sum_univ_five]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    exact hFO.symm

  have r1' : resT E.a₁ = E₀.a₁ := r1
  have r2' : resT E.a₂ = E₀.a₂ := r2
  have r3' : resT E.a₃ = E₀.a₃ := r3
  have r4' : resT E.a₄ = E₀.a₄ := r4
  have r6' : resT E.a₆ = E₀.a₆ := r6
  have hLres : ∀ i j, resT (L2Aux.LEmat E i j) = L2Aux.LEmat E₀ i j := by
    intro i j
    unfold L2Aux.LEmat
    fin_cases i <;> fin_cases j <;> simp [r1', r2', r3', r4', r6', map_ofNat]
  have hid : ∀ i l, (L2Aux.LEmat E₀ * LinearMap.toMatrix' g) i l - (1 : Matrix (Fin 5) (Fin 5) k) i l = w i * c l := by
    intro i l
    have e := congrFun (hgw (Pi.single l 1)) i
    rw [Pi.sub_apply, Pi.smul_apply, H2Aux.functional_apply, smul_eq_mul] at e
    rw [Finset.sum_eq_single l (fun j _ hj => by rw [Pi.single_eq_of_ne hj, mul_zero])
      (fun h => absurd (Finset.mem_univ l) h), Pi.single_eq_same, mul_one] at e
    rw [← L2Aux.LEmat_mulVec] at e
    have e1 : (L2Aux.LEmat E₀ * LinearMap.toMatrix' g) i l = (L2Aux.LEmat E₀).mulVec (g (Pi.single l 1)) i := by
      rw [Matrix.mul_apply, Matrix.mulVec, dotProduct]
      try (refine Finset.sum_congr rfl fun j _ => ?_; rw [LinearMap.toMatrix'_apply])
    rw [e1, Matrix.one_apply, show (if i = l then (1 : k) else 0) = (Pi.single l (1 : k) : Fin 5 → k) i by
      rw [Pi.single_apply], e, mul_comm]
  obtain ⟨m, hmI, hLm⟩ := L2Aux.lift_solve I hI resT hresT hkerT (L2Aux.LEmat E₀) (L2Aux.LEmat E) hLres c t ht
    (LinearMap.toMatrix' g) w hid δ hδI hsum

  have hmm : ∀ i j, m i * m j = 0 := fun i j => hImul _ _ (hmI i) (hIm (hmI j))
  obtain ⟨C, hCu, hCr, hCs, hCt, hCE⟩ := L2Aux.exists_variableChange_smul_eq E m hmm
  refine ⟨C, ?_, ?_⟩
  · apply WeierstrassCurve.VariableChange.ext
    · apply Units.ext
      show Ideal.Quotient.mk I ((C.u : Tˣ) : T) = 1
      rw [hCu, map_sub, map_one, Ideal.Quotient.eq_zero_iff_mem.mpr (hmI 0), sub_zero]
    · show Ideal.Quotient.mk I C.r = 0; rw [hCr]; exact Ideal.Quotient.eq_zero_iff_mem.mpr (hmI 1)
    · show Ideal.Quotient.mk I C.s = 0; rw [hCs]; exact Ideal.Quotient.eq_zero_iff_mem.mpr (hmI 2)
    · show Ideal.Quotient.mk I C.t = 0; rw [hCt]; exact Ideal.Quotient.eq_zero_iff_mem.mpr (hmI 3)
  · rw [hCE, hLm, hδ]
    refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_ <;> simp

end S_WeierstrassCurve_exists_variableChange_map_mk_eq_one_and_smul_eq_of_lawIso_of_mul_maximalIdeal_eq_bot_of_prime
end P2MW
export P2MW.S_WeierstrassCurve_exists_variableChange_map_mk_eq_one_and_smul_eq_of_lawIso_of_mul_maximalIdeal_eq_bot_of_prime (solution)
