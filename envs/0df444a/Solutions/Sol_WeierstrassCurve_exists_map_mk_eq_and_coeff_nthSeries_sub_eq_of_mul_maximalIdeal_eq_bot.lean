-- Prove2me | solution 1 for WeierstrassCurve.exists_map_mk_eq_and_coeff_nthSeries_sub_eq_of_mul_maximalIdeal_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/ce4616a6-06f7-596f-9ad2-348f87f3b036

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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_map_mk_eq_and_coeff_nthSeries_sub_eq_of_mul_maximalIdeal_eq_bot
p2m_attr_erase "simp" "ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ"

set_option autoImplicit false

open FormalGroup IsLocalRing

namespace DerivAux

open WeierstrassCurve

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

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) (k : Type) [Field k] [CharP k q]
    (E₀ : WeierstrassCurve k) [E₀.IsElliptic] (hE₀ : E₀.formalGroup.IsDrinfeldBasisAdic ⊥ q 0 0)
    (T : Type) [CommRing T] [IsLocalRing T] (I : Ideal T) (hI : I * maximalIdeal T = ⊥) (hIm : I ≤ maximalIdeal T)
    (resT : T →+* k) (hresT : Function.Surjective resT) (hkerT : RingHom.ker resT = maximalIdeal T)
    (E : WeierstrassCurve T) (hE : E.map resT = E₀) (c : T) (hc : c ∈ I) :
    ∃ E' : WeierstrassCurve T, E'.map (Ideal.Quotient.mk I) = E.map (Ideal.Quotient.mk I) ∧
      ∀ (G G' : FormalGroup T), G.toPowerSeries = E.formalGroupLawFixed →
        G'.toPowerSeries = E'.formalGroupLawFixed →
          PowerSeries.coeff q (G'.nthSeries q) - PowerSeries.coeff q (G.nthSeries q) = c := by
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

  obtain ⟨c₁, hc₁0, hF1⟩ := WeierstrassCurve.exists_coeff_nthSeries_eq_mul_hasseInvariant q hq
  have hck : (c₁ : k) ≠ 0 := fun h =>
    hc₁0 ((ZMod.intCast_zmod_eq_zero_iff_dvd c₁ q).mpr ((CharP.intCast_eq_zero_iff k q c₁).mp h))
  haveI : IsAdicComplete (⊥ : Ideal k) k := inferInstance
  obtain ⟨u₀, hu₀, hq0⟩ := (FormalGroup.isDrinfeldBasisAdic_zero_zero_iff (⊥ : Ideal k) E₀.formalGroup q).mp hE₀
  have hH0 : E₀.hasseInvariant q = 0 := by
    have h1 := hF1 k E₀ E₀.isUnit_Δ E₀.formalGroup rfl
    rw [hq0, PowerSeries.coeff_mul_X_pow', if_neg (not_le.mpr hqlt)] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left hck
  have hHε : Eε.hasseInvariant q = 0 := by rw [hEε, DerivAux.hasseInvariant_map, hH0, map_zero]
  have hcoefε : PowerSeries.coeff q (Gε.nthSeries q) = 0 := by
    rw [hF1 (DualNumber k) Eε (by rw [hEε, WeierstrassCurve.map_Δ]; exact E₀.isUnit_Δ.map _) Gε hGεser, hHε, mul_zero]

  have hsnd_c : ∀ (a : k) (x : DualNumber k), TrivSqZeroExt.snd ((algebraMap k (DualNumber k) a) * x) =
      a * TrivSqZeroExt.snd x := by
    intro a x
    rw [hinl, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, smul_zero, _root_.add_zero, smul_eq_mul]
  have hsnd_int : ∀ (x : DualNumber k), TrivSqZeroExt.snd ((c₁ : DualNumber k) * x) = (c₁ : k) * TrivSqZeroExt.snd x := by
    intro x; rw [← map_intCast (algebraMap k (DualNumber k)) c₁, hsnd_c]

  obtain ⟨cv, hcv⟩ := WeierstrassCurve.exists_forall_coeff_nthSeries_sub_eq_sum_of_mul_maximalIdeal_eq_bot q k E₀

  have hFOε : ∀ (E' : WeierstrassCurve (DualNumber k)) (G' : FormalGroup (DualNumber k)),
      E'.map π = E₀ → G'.toPowerSeries = E'.formalGroupLawFixed →
      TrivSqZeroExt.snd (PowerSeries.coeff q (G'.nthSeries q)) =
        ∑ i, cv i * (![E'.a₁.snd, E'.a₂.snd, E'.a₃.snd, E'.a₄.snd, E'.a₆.snd] : Fin 5 → k) i := by
    intro E' G' hE' hG'
    obtain ⟨e1, e2, e3, e4, e6⟩ := WeierstrassCurve.ext_iff.mp hE'
    have key : ∀ (x : DualNumber k) (a : k), π x = a → x - TrivSqZeroExt.inl a ∈ maximalIdeal (DualNumber k) := by
      intro x a hx; rw [hmemε, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_inl, ← hπapp, hx, sub_self]
    have e := hcv (DualNumber k) (maximalIdeal (DualNumber k)) hsqε le_rfl π hπsurj hkerε Eε E' hEεπ (by
        obtain ⟨f1, f2, f3, f4, f6⟩ := hEεa
        refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_
        · show Ideal.Quotient.mk _ E'.a₁ = Ideal.Quotient.mk _ Eε.a₁; rw [f1, Ideal.Quotient.eq]; exact key _ _ e1
        · show Ideal.Quotient.mk _ E'.a₂ = Ideal.Quotient.mk _ Eε.a₂; rw [f2, Ideal.Quotient.eq]; exact key _ _ e2
        · show Ideal.Quotient.mk _ E'.a₃ = Ideal.Quotient.mk _ Eε.a₃; rw [f3, Ideal.Quotient.eq]; exact key _ _ e3
        · show Ideal.Quotient.mk _ E'.a₄ = Ideal.Quotient.mk _ Eε.a₄; rw [f4, Ideal.Quotient.eq]; exact key _ _ e4
        · show Ideal.Quotient.mk _ E'.a₆ = Ideal.Quotient.mk _ Eε.a₆; rw [f6, Ideal.Quotient.eq]; exact key _ _ e6)
      Gε G' hGεser hG' (fun i => algebraMap k (DualNumber k) (cv i)) (fun i => hres (cv i))
    have e' := congrArg TrivSqZeroExt.snd e
    rw [TrivSqZeroExt.snd_sub, hcoefε, TrivSqZeroExt.snd_zero, sub_zero] at e'
    rw [e']
    obtain ⟨f1, f2, f3, f4, f6⟩ := hEεa
    simp only [TrivSqZeroExt.snd_add, hsnd_c, TrivSqZeroExt.snd_sub, f1, f2, f3, f4, f6, TrivSqZeroExt.snd_inl, sub_zero,
      Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    try rfl

  have hcomp : LinearMap.range (H2Aux.tangentMap E₀) ≤ LinearMap.ker (H2Aux.functional cv) := by
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
    rw [hF1 (DualNumber k) E' hΔ' G' hG', hE', WeierstrassCurve.hasseInvariant_variableChange, hHε, mul_zero, mul_zero,
      TrivSqZeroExt.snd_zero] at e
    have hsm := H2Aux.Cinf_smul E₀ (m 0) (m 1) (m 2) (m 3)
    rw [← hEε] at hsm
    rw [hsm] at e
    simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, _root_.zero_add] at e
    rw [e, H2Aux.tangentMap_apply]
    all_goals (simp only [Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; try rfl)

  obtain ⟨E₂, hE₂, hsnd₂⟩ := WeierstrassCurve.exists_map_fstHom_eq_and_snd_hasseInvariant_ne_zero q hq k E₀ hH0
  have hΔ₂ : IsUnit E₂.Δ := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, ← hπapp, ← WeierstrassCurve.map_Δ, hE₂]; exact E₀.isUnit_Δ
  obtain ⟨G₂, hG₂⟩ := L2Aux.exists_law _ E₂ hΔ₂
  set v₂ : Fin 5 → k := ![E₂.a₁.snd, E₂.a₂.snd, E₂.a₃.snd, E₂.a₄.snd, E₂.a₆.snd] with hv₂
  have hlam₂ : H2Aux.functional cv v₂ ≠ 0 := by
    rw [H2Aux.functional_apply, hv₂, ← hFOε E₂ G₂ hE₂ hG₂, hF1 (DualNumber k) E₂ hΔ₂ G₂ hG₂, hsnd_int]
    exact mul_ne_zero hck hsnd₂

  have hci : ∃ i, cv i ≠ 0 := by
    by_contra h
    push_neg at h
    apply hlam₂
    rw [H2Aux.functional_apply]
    exact Finset.sum_eq_zero fun i _ => by rw [h i, zero_mul]
  obtain ⟨i₀, hi₀⟩ := hci

  choose t ht using fun i : Fin 5 => hresT (cv i)
  have htu : IsUnit (t i₀) := by
    by_contra hu
    have : t i₀ ∈ maximalIdeal T := (IsLocalRing.mem_maximalIdeal _).mpr hu
    rw [hmem, ht] at this; exact hi₀ this
  obtain ⟨tu, htu'⟩ := htu
  set d : T := ((tu⁻¹ : Tˣ) : T) * c with hd
  have hdI : d ∈ I := I.mul_mem_left _ hc
  set δ : Fin 5 → T := Pi.single i₀ d with hδ
  have hδI : ∀ i, δ i ∈ I := by
    intro i; rw [hδ]; by_cases h : i = i₀
    · subst h; rw [Pi.single_eq_same]; exact hdI
    · rw [Pi.single_eq_of_ne h]; exact I.zero_mem
  let E' : WeierstrassCurve T := ⟨E.a₁ + δ 0, E.a₂ + δ 1, E.a₃ + δ 2, E.a₄ + δ 3, E.a₆ + δ 4⟩
  have hEE' : E'.map (Ideal.Quotient.mk I) = E.map (Ideal.Quotient.mk I) := by
    have key : ∀ (x : T) (i : Fin 5), Ideal.Quotient.mk I (x + δ i) = Ideal.Quotient.mk I x := by
      intro x i; rw [Ideal.Quotient.eq, add_sub_cancel_left]; exact hδI i
    exact WeierstrassCurve.ext (key _ _) (key _ _) (key _ _) (key _ _) (key _ _)
  refine ⟨E', hEE', fun G G' hG hG' => ?_⟩
  rw [hcv T I hI hIm resT hresT hkerT E E' hE hEE' G G' hG hG' t ht]
  show t 0 * (E.a₁ + δ 0 - E.a₁) + t 1 * (E.a₂ + δ 1 - E.a₂) + t 2 * (E.a₃ + δ 2 - E.a₃) + t 3 * (E.a₄ + δ 3 - E.a₄) +
      t 4 * (E.a₆ + δ 4 - E.a₆) = c
  simp only [add_sub_cancel_left]
  have hsum : ∑ i, t i * δ i = c := by
    rw [Finset.sum_eq_single i₀, hδ, Pi.single_eq_same, hd, ← mul_assoc, ← htu', Units.mul_inv, one_mul]
    · intro j _ hj; rw [hδ, Pi.single_eq_of_ne hj, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i₀) h
  rw [← hsum, Fin.sum_univ_five]

end S_WeierstrassCurve_exists_map_mk_eq_and_coeff_nthSeries_sub_eq_of_mul_maximalIdeal_eq_bot
end P2MW
export P2MW.S_WeierstrassCurve_exists_map_mk_eq_and_coeff_nthSeries_sub_eq_of_mul_maximalIdeal_eq_bot (solution)
