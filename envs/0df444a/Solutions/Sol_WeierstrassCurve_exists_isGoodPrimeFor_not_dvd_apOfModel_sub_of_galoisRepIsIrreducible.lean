-- Prove2me | solution 1 for WeierstrassCurve.exists_isGoodPrimeFor_not_dvd_apOfModel_sub_of_galoisRepIsIrreducible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/fbc1523c-ab24-5947-a424-331905a1c3de

import Mathlib
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Theorems.Thm_Subgroup_exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen
import Theorems.Thm_WeierstrassCurve_finrank_zmod_torsionBy_point_eq_two
import Theorems.Thm_WeierstrassCurve_galoisTrace_frobenius_eq_apOfModel_of_isIntegralModelOf
import Theorems.Thm_WeierstrassCurve_det_galoisRepModuleEnd_frobenius_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_isGoodPrimeFor_not_dvd_apOfModel_sub_of_galoisRepIsIrreducible
p2m_attr_erase "instance" "FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow AlgebraicClosure.Rat.isGalois WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two FrobeniusEndo.linePencil_apply WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.mem_fibSet WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal"

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

namespace W8C0

open Module

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

lemma apply_basis_eq (b : Basis (Fin 2) k V) (f : V →ₗ[k] V) (j : Fin 2) :
    f (b j) = (LinearMap.toMatrix b b f) 0 j • b 0 + (LinearMap.toMatrix b b f) 1 j • b 1 := by
  have h := (b.sum_repr (f (b j))).symm
  rw [Fin.sum_univ_two] at h
  simpa [LinearMap.toMatrix_apply] using h

lemma apply_comb (b : Basis (Fin 2) k V) (f : V →ₗ[k] V) (x0 x1 : k) :
    f (x0 • b 0 + x1 • b 1) =
      (LinearMap.toMatrix b b f 0 0 * x0 + LinearMap.toMatrix b b f 0 1 * x1) • b 0 +
      (LinearMap.toMatrix b b f 1 0 * x0 + LinearMap.toMatrix b b f 1 1 * x1) • b 1 := by
  simp only [map_add, map_smul, apply_basis_eq b f]
  module

lemma repr_comb_zero (b : Basis (Fin 2) k V) (x0 x1 : k) :
    b.repr (x0 • b 0 + x1 • b 1) 0 = x0 := by
  simp

lemma repr_comb_one (b : Basis (Fin 2) k V) (x0 x1 : k) :
    b.repr (x0 • b 0 + x1 • b 1) 1 = x1 := by
  simp

lemma comb_ne_zero (b : Basis (Fin 2) k V) {x0 x1 : k} (h : x0 ≠ 0 ∨ x1 ≠ 0) :
    x0 • b 0 + x1 • b 1 ≠ 0 := by
  intro h0
  have e0 := repr_comb_zero b x0 x1
  have e1 := repr_comb_one b x0 x1
  simp only [h0, _root_.map_zero, Finsupp.coe_zero, Pi.zero_apply] at e0 e1
  rcases h with h | h
  · exact h e0.symm
  · exact h e1.symm

theorem exists_fixed_of_trace_eq_one_add_det (h2 : finrank k V = 2) (f : V →ₗ[k] V)
    (h : LinearMap.trace k V f = 1 + LinearMap.det f) : ∃ v : V, v ≠ 0 ∧ f v = v := by
  classical
  haveI : Module.Finite k V := Module.finite_of_finrank_eq_succ h2
  let b : Basis (Fin 2) k V := Module.finBasisOfFinrankEq k V h2
  set A := LinearMap.toMatrix b b f with hA
  have htr : LinearMap.trace k V f = A 0 0 + A 1 1 := by
    rw [LinearMap.trace_eq_matrix_trace k b, Matrix.trace_fin_two]
  have hdet : LinearMap.det f = A 0 0 * A 1 1 - A 0 1 * A 1 0 := by
    rw [← LinearMap.det_toMatrix b, Matrix.det_fin_two]
  rw [htr, hdet] at h
  by_cases hc : A 0 1 ≠ 0 ∨ 1 - A 0 0 ≠ 0
  · refine ⟨A 0 1 • b 0 + (1 - A 0 0) • b 1, comb_ne_zero b hc, ?_⟩
    rw [apply_comb b f, ← hA]
    congr 1
    · congr 1; ring
    · congr 1; linear_combination h
  · push Not at hc
    obtain ⟨h01, h00⟩ := hc
    have h00' : A 0 0 = 1 := by linear_combination -h00
    by_cases hc' : 1 - A 1 1 ≠ 0 ∨ A 1 0 ≠ 0
    · refine ⟨(1 - A 1 1) • b 0 + A 1 0 • b 1, comb_ne_zero b hc', ?_⟩
      rw [apply_comb b f, ← hA]
      congr 1
      · congr 1; rw [h01, h00']; ring
      · congr 1; ring
    · push Not at hc'
      obtain ⟨h11, h10⟩ := hc'
      refine ⟨(1 : k) • b 0 + (0 : k) • b 1, comb_ne_zero b (Or.inl one_ne_zero), ?_⟩
      rw [apply_comb b f, ← hA]
      congr 1
      · congr 1; rw [h00']; ring
      · congr 1; rw [h10]; ring

lemma matrix_rel_of_fixed (b : Basis (Fin 2) k V) (f : V →ₗ[k] V) {v : V} (hv : v ≠ 0)
    (hfv : f v = v) :
    (LinearMap.toMatrix b b f 0 0 - 1) * (LinearMap.toMatrix b b f 1 1 - 1)
      - LinearMap.toMatrix b b f 0 1 * LinearMap.toMatrix b b f 1 0 = 0 := by
  classical
  have hd : (LinearMap.toMatrix b b (f - 1)).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨b.repr v, ?_, ?_⟩
    · intro h0
      apply hv
      have : b.repr v = 0 := Finsupp.ext fun i => by simpa using congrFun h0 i
      simpa using this
    · rw [LinearMap.toMatrix_mulVec_repr]
      ext i
      simp [hfv]
  rw [map_sub, LinearMap.toMatrix_one, Matrix.det_fin_two] at hd
  simpa [Matrix.sub_apply, Matrix.one_apply] using hd

theorem exists_stable_line (h2 : finrank k V = 2) {G : Type*} [Group G]
    (ρ : G →* Module.End k V) (hfix : ∀ g, ∃ v : V, v ≠ 0 ∧ ρ g v = v) :
    ∃ L : Submodule k V, L ≠ ⊥ ∧ L ≠ ⊤ ∧ ∀ g, ∀ v ∈ L, ρ g v ∈ L := by
  classical
  haveI : Module.Finite k V := Module.finite_of_finrank_eq_succ h2
  have hinv : ∀ g, ρ g * ρ g⁻¹ = 1 := fun g => by rw [← map_mul, mul_inv_cancel, map_one]
  have hinv' : ∀ g, ρ g⁻¹ * ρ g = 1 := fun g => by rw [← map_mul, inv_mul_cancel, map_one]
  have line_ne_bot : ∀ v : V, v ≠ 0 → (k ∙ v) ≠ ⊥ := fun v hv h =>
    hv ((Submodule.span_singleton_eq_bot).mp h)
  have line_ne_top : ∀ v : V, v ≠ 0 → (k ∙ v) ≠ ⊤ := by
    intro v hv h
    have h1 : finrank k (k ∙ v) = 1 := finrank_span_singleton hv
    rw [h] at h1
    rw [finrank_top] at h1
    omega
  by_cases hK : ∃ g₀, LinearMap.det (ρ g₀) = 1 ∧ ρ g₀ ≠ 1
  ·
    obtain ⟨g₀, hdet₀, hne⟩ := hK
    obtain ⟨v₀, hv₀, hfix₀⟩ := hfix g₀
    obtain ⟨w, hw⟩ : ∃ w : V, w ∉ (k ∙ v₀) := by
      by_contra hall
      push Not at hall
      exact line_ne_top v₀ hv₀ (Submodule.eq_top_iff'.mpr hall)
    have hli : LinearIndependent k ![v₀, w] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      by_cases ht : t = 0
      · subst ht
        simp only [zero_smul, add_zero, smul_eq_zero] at hst
        exact ⟨hst.resolve_right hv₀, rfl⟩
      · exfalso
        apply hw
        rw [Submodule.mem_span_singleton]
        refine ⟨-(s / t), ?_⟩
        have : t • w = -(s • v₀) := eq_neg_of_add_eq_zero_right hst
        calc -(s / t) • v₀ = t⁻¹ • (-(s • v₀)) := by rw [smul_neg, smul_smul, neg_smul]; ring_nf
          _ = t⁻¹ • (t • w) := by rw [this]
          _ = w := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
    let b : Basis (Fin 2) k V :=
      basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])
    have hb0 : b 0 = v₀ := by simp [b]
    have hb1 : b 1 = w := by simp [b]
    set Am : G → Matrix (Fin 2) (Fin 2) k := fun g => LinearMap.toMatrix b b (ρ g) with hAm
    have Amul : ∀ g h, Am (g * h) = Am g * Am h := by
      intro g h; simp only [Am, map_mul, LinearMap.toMatrix_mul]
    have Adet : ∀ g, Am g 0 0 * Am g 1 1 - Am g 0 1 * Am g 1 0 = LinearMap.det (ρ g) := by
      intro g; rw [← LinearMap.det_toMatrix b, Matrix.det_fin_two]
    have Afix : ∀ g, (Am g 0 0 - 1) * (Am g 1 1 - 1) - Am g 0 1 * Am g 1 0 = 0 := by
      intro g
      obtain ⟨v, hv, hv'⟩ := hfix g
      exact matrix_rel_of_fixed b (ρ g) hv hv'

    have hρb0 : ρ g₀ (b 0) = b 0 := by rw [hb0]; exact hfix₀
    have h00 : Am g₀ 0 0 = 1 := by simp [Am, LinearMap.toMatrix_apply, hρb0]
    have h10 : Am g₀ 1 0 = 0 := by simp [Am, LinearMap.toMatrix_apply, hρb0]
    have h11 : Am g₀ 1 1 = 1 := by
      have := Adet g₀; rw [h00, h10, hdet₀] at this; linear_combination this
    have hβ : Am g₀ 0 1 ≠ 0 := by
      intro h01
      apply hne
      have : Am g₀ = 1 := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]
      have h1 : LinearMap.toMatrix b b (ρ g₀) = LinearMap.toMatrix b b 1 := by
        rw [LinearMap.toMatrix_one]; exact this
      exact (LinearMap.toMatrix b b).injective h1

    have hunip : ∀ g, LinearMap.det (ρ g) = 1 →
        Am g 1 0 = 0 ∧ Am g 0 0 = 1 ∧ Am g 1 1 = 1 := by
      intro g hg
      have e1 := Afix g
      have e2 := Adet g
      rw [hg] at e2

      have e3 := Afix (g₀ * g)
      have e4 := Adet (g₀ * g)
      rw [map_mul, map_mul, hdet₀, hg, one_mul] at e4
      have p00 : Am (g₀ * g) 0 0 = Am g 0 0 + Am g₀ 0 1 * Am g 1 0 := by
        rw [Amul]; simp [Matrix.mul_apply, Fin.sum_univ_two, h00]
      have p11 : Am (g₀ * g) 1 1 = Am g 1 1 := by
        rw [Amul]; simp [Matrix.mul_apply, Fin.sum_univ_two, h10, h11]
      have p01 : Am (g₀ * g) 0 1 = Am g 0 1 + Am g₀ 0 1 * Am g 1 1 := by
        rw [Amul]; simp [Matrix.mul_apply, Fin.sum_univ_two, h00]
      have p10 : Am (g₀ * g) 1 0 = Am g 1 0 := by
        rw [Amul]; simp [Matrix.mul_apply, Fin.sum_univ_two, h10, h11]
      rw [p00, p11, p01, p10] at e3 e4

      have htr1 : Am g 0 0 + Am g 1 1 = 2 := by linear_combination e2 - e1
      have htr2 : Am g 0 0 + Am g₀ 0 1 * Am g 1 0 + Am g 1 1 = 2 := by
        linear_combination e4 - e3
      have hc0 : Am g 1 0 = 0 := by
        have : Am g₀ 0 1 * Am g 1 0 = 0 := by linear_combination htr2 - htr1
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h hβ
        · exact h
      have ha : Am g 0 0 = 1 := by
        have hsq : (Am g 0 0 - 1) ^ 2 = 0 := by
          rw [hc0] at e2
          linear_combination (Am g 0 0) * htr1 - e2
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
        linear_combination this
      refine ⟨hc0, ha, ?_⟩
      linear_combination htr1 - ha

    have hupper : ∀ g, Am g 1 0 = 0 := by
      intro g
      have hk : LinearMap.det (ρ (g * g₀ * g⁻¹)) = 1 := by
        rw [map_mul, map_mul, map_mul, map_mul, hdet₀, mul_one, ← map_mul, hinv, map_one]
      obtain ⟨k10, k00, k11⟩ := hunip _ hk
      have hprod : Am (g * g₀ * g⁻¹) * Am g = Am g * Am g₀ := by
        rw [← Amul, ← Amul]
        congr 1
        group
      have := congrFun (congrFun hprod 1) 1
      simp only [Matrix.mul_apply, Fin.sum_univ_two, k10, k11, h11, zero_mul, one_mul,
        zero_add, mul_one] at this

      have h0 : Am g 1 0 * Am g₀ 0 1 = 0 := by linear_combination -this
      rcases mul_eq_zero.mp h0 with h | h
      · exact h
      · exact absurd h hβ
    refine ⟨k ∙ v₀, line_ne_bot v₀ hv₀, line_ne_top v₀ hv₀, ?_⟩
    intro g v hv
    rw [Submodule.mem_span_singleton] at hv
    obtain ⟨c, rfl⟩ := hv
    rw [map_smul]
    refine Submodule.smul_mem _ _ ?_
    have := apply_basis_eq b (ρ g) 0
    rw [hb0] at this
    rw [this, show LinearMap.toMatrix b b (ρ g) 1 0 = Am g 1 0 from rfl, hupper g, zero_smul,
      add_zero]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v₀)
  ·
    push Not at hK
    have hcomm : ∀ g h, ρ g * ρ h = ρ h * ρ g := by
      intro g h
      have h1 : LinearMap.det (ρ (g * h * g⁻¹ * h⁻¹)) = 1 := by
        rw [map_mul, map_mul, map_mul, map_mul, map_mul, map_mul,
          mul_comm (LinearMap.det (ρ g)) (LinearMap.det (ρ h)), mul_assoc, mul_assoc,
          ← mul_assoc (LinearMap.det (ρ g)), ← map_mul, hinv, map_one, one_mul, ← map_mul,
          hinv, map_one]
      have h2' := hK _ h1
      calc ρ g * ρ h = ρ (g * h) := (map_mul ρ g h).symm
        _ = ρ (g * h * g⁻¹ * h⁻¹ * (h * g)) := by congr 1; group
        _ = ρ (g * h * g⁻¹ * h⁻¹) * ρ (h * g) := map_mul ρ _ _
        _ = ρ h * ρ g := by rw [h2', one_mul, map_mul]
    by_cases htriv : ∀ g, ρ g = 1
    · obtain ⟨v, hv, -⟩ := hfix 1
      refine ⟨k ∙ v, line_ne_bot v hv, line_ne_top v hv, fun g x hx => ?_⟩
      rw [htriv g]; simpa using hx
    · push Not at htriv
      obtain ⟨g₁, hg₁⟩ := htriv
      refine ⟨LinearMap.ker (ρ g₁ - 1), ?_, ?_, ?_⟩
      · obtain ⟨v, hv, hv'⟩ := hfix g₁
        intro hbot
        apply hv
        have : v ∈ LinearMap.ker (ρ g₁ - 1) := by
          rw [LinearMap.mem_ker, LinearMap.sub_apply, hv', Module.End.one_apply, sub_self]
        rw [hbot] at this
        exact (Submodule.mem_bot k).mp this
      · intro htop
        apply hg₁
        rw [LinearMap.ker_eq_top, sub_eq_zero] at htop
        exact htop
      · intro g v hv
        rw [LinearMap.mem_ker] at hv ⊢
        have := congrArg (fun f => f v) (hcomm g₁ g)
        simp only [Module.End.mul_apply] at this
        rw [LinearMap.sub_apply, Module.End.one_apply] at hv ⊢
        rw [sub_eq_zero] at hv ⊢
        rw [this, hv]

theorem isIntegral_algebraicClosure_rat : Algebra.IsIntegral ℚ (AlgebraicClosure ℚ) := by
  have h := Subsingleton.elim (AlgebraicClosure.instAlgebra ℚ) (DivisionRing.toRatAlgebra)
  have := AlgebraicClosure.isAlgebraic ℚ
  rw [h] at this
  exact Algebra.IsAlgebraic.isIntegral

theorem isOpen_stabilizer_point (E : WeierstrassCurve ℚ)
    (P : (E.baseChange (AlgebraicClosure ℚ)).toAffine.Point) :
    IsOpen ((MulAction.stabilizer (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) P :
      Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
        Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) := by
  haveI := isIntegral_algebraicClosure_rat
  cases P with
  | zero =>
    have : (MulAction.stabilizer (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (Point.zero : (E.baseChange (AlgebraicClosure ℚ)).toAffine.Point)) = ⊤ := by
      ext σ
      simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_top, iff_true]
      exact smul_zero (A := (E.baseChange (AlgebraicClosure ℚ)).toAffine.Point) σ
    rw [this]
    exact isOpen_univ
  | some x y h =>
    apply Subgroup.isOpen_mono (H₁ := MulAction.stabilizer _ x ⊓ MulAction.stabilizer _ y)
    · intro σ hσ
      rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff] at hσ
      rw [MulAction.mem_stabilizer_iff, algEquiv_smul_def, Point.map_some]
      have hx : σ x = x := hσ.1
      have hy : σ y = y := hσ.2
      show Point.some (σ x) (σ y) _ = Point.some x y h
      congr 1
    · exact (stabilizer_isOpen_of_isIntegral x).inter (stabilizer_isOpen_of_isIntegral y)

theorem isOpen_ker_galoisRepModuleEnd (E : WeierstrassCurve ℚ) (p : ℕ)
    [Finite (Submodule.torsionBy ℤ (E.baseChange (AlgebraicClosure ℚ)).toAffine.Point p)] :
    IsOpen (((galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ E p).ker :
      Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
        Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) := by
  have hset : (((galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ E p).ker :
      Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
        Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) =
      ⋂ x : Submodule.torsionBy ℤ (E.baseChange (AlgebraicClosure ℚ)).toAffine.Point p,
        ((MulAction.stabilizer (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (x : (E.baseChange (AlgebraicClosure ℚ)).toAffine.Point) : Subgroup _) : Set _) := by
    ext σ
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, MulAction.mem_stabilizer_iff]
    constructor
    · intro h x
      have := LinearMap.congr_fun h x
      simp only [galoisRepModuleEnd_apply, Module.End.one_apply] at this
      exact congrArg Subtype.val this
    · intro h
      apply LinearMap.ext
      intro x
      simp only [galoisRepModuleEnd_apply, Module.End.one_apply]
      exact Subtype.ext (h x)
  rw [hset]
  exact isOpen_iInter_of_finite fun x => isOpen_stabilizer_point E _

theorem main (E : WeierstrassCurve ℚ) [E.IsElliptic] {W : WeierstrassCurve ℤ}
    (hW : W.IsIntegralModelOf E) {p : ℕ} (hp : p.Prime)
    (hirr : GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ E p)
    {M : ℕ} (hM : 0 < M) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ W.IsGoodPrimeFor ℓ ∧ ¬ ℓ ∣ M ∧
      ¬ (p : ℤ) ∣ W.apOfModel ℓ - ((ℓ : ℤ) + 1) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hcon
  push Not at hcon

  set V := Submodule.torsionBy ℤ (E.baseChange (AlgebraicClosure ℚ)).toAffine.Point p with hV
  have hfr : Module.finrank (ZMod p) V = 2 :=
    E.finrank_zmod_torsionBy_point_eq_two hp (by exact_mod_cast hp.ne_zero)
  haveI : Module.Finite (ZMod p) V := Module.finite_of_finrank_eq_succ hfr
  haveI : Finite V := Module.finite_of_finite (ZMod p)
  set ρ := galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ E p with hρ

  have hΔ : W.Δ ≠ 0 := by
    obtain ⟨C, hC⟩ := hW
    intro h0
    have h1 : (W.map (Int.castRingHom ℚ)).Δ = 0 := by rw [map_Δ, h0, _root_.map_zero]
    rw [← hC, variableChange_Δ] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exact (Units.ne_zero _) (pow_eq_zero_iff (by norm_num) |>.mp h)
    · exact E.isUnit_Δ.ne_zero h

  have hfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∃ v : V, v ≠ 0 ∧ ρ σ v = v := by
    intro σ
    have hM' : 0 < M * p * W.Δ.natAbs :=
      Nat.mul_pos (Nat.mul_pos hM hp.pos) (Int.natAbs_pos.mpr hΔ)
    obtain ⟨ℓ, A, τ, g, n, hℓ, hℓM, hA, hτ, hmem⟩ :=
      ρ.ker.exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen
        (isOpen_ker_galoisRepModuleEnd E p) σ hM'
    have hℓM0 : ¬ ℓ ∣ M := fun h => hℓM (Dvd.dvd.mul_right (Dvd.dvd.mul_right h _) _)
    have hℓp : ℓ ≠ p := by
      rintro rfl
      exact hℓM (Dvd.dvd.mul_right (Dvd.intro_left _ rfl) _)
    have hgood : W.IsGoodPrimeFor ℓ := by
      intro h
      exact hℓM (Dvd.dvd.mul_left (Int.natCast_dvd.mp h) _)
    have htr := E.galoisTrace_frobenius_eq_apOfModel_of_isIntegralModelOf hW hp hℓ hgood hℓp A hA τ hτ
    have hdet := E.det_galoisRepModuleEnd_frobenius_eq hp hℓ hℓp A hA τ hτ
    have hcong : ((W.apOfModel ℓ : ℤ) : ZMod p) = (ℓ : ZMod p) + 1 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (hcon ℓ hℓ hgood hℓM0)
      push_cast at this
      linear_combination this
    have htrace : LinearMap.trace (ZMod p) V (ρ τ) = 1 + LinearMap.det (ρ τ) := by
      rw [hdet, ← galoisTrace_def, htr, hcong, add_comm]
    obtain ⟨v, hv, hτv⟩ := exists_fixed_of_trace_eq_one_add_det hfr (ρ τ) htrace

    have hστ : ρ σ = ρ g * ρ τ ^ n * ρ g⁻¹ := by
      have h1 : ρ (g * τ ^ n * g⁻¹ * σ⁻¹) = 1 := hmem
      have h2 : ρ (g * τ ^ n * g⁻¹) = ρ σ := by
        calc ρ (g * τ ^ n * g⁻¹) = ρ (g * τ ^ n * g⁻¹ * σ⁻¹ * σ) := by congr 1; group
          _ = ρ σ := by rw [map_mul, h1, one_mul]
      rw [← h2, map_mul, map_mul, map_pow]
    have hginv : ∀ x : V, ρ g⁻¹ (ρ g x) = x := fun x => by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    have hτn : (ρ τ ^ n) v = v := by
      rw [Module.End.pow_apply]
      exact Function.iterate_fixed hτv n
    refine ⟨ρ g v, ?_, ?_⟩
    · intro h0
      apply hv
      rw [← hginv v, h0, _root_.map_zero]
    · rw [hστ, Module.End.mul_apply, Module.End.mul_apply, hginv, hτn]

  obtain ⟨L, hLbot, hLtop, hLstab⟩ := exists_stable_line hfr ρ hfix

  rcases hirr.2 L (fun σ x hx => hLstab σ x hx) with h | h
  · exact hLbot h
  · exact hLtop h

end W8C0

theorem solution
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {W : WeierstrassCurve ℤ} (hW : W.IsIntegralModelOf E)
    {p : ℕ} (hp : p.Prime)
    (hirr : GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ E p)
    {M : ℕ} (hM : 0 < M) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ W.IsGoodPrimeFor ℓ ∧ ¬ ℓ ∣ M ∧
      ¬ (p : ℤ) ∣ W.apOfModel ℓ - ((ℓ : ℤ) + 1) :=
  W8C0.main E hW hp hirr hM

end S_WeierstrassCurve_exists_isGoodPrimeFor_not_dvd_apOfModel_sub_of_galoisRepIsIrreducible
end P2MW
export P2MW.S_WeierstrassCurve_exists_isGoodPrimeFor_not_dvd_apOfModel_sub_of_galoisRepIsIrreducible (solution)
