-- Prove2me | solution 1 for WeierstrassCurve.exists_mem_rationalHomSet_comp_eq_of_ker_le_of_separable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/1b12b4b7-4142-590a-8798-f095b127028b

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_Psi2Sq_ne_zero_of_isElliptic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_comp_eq_of_ker_le_of_separable

p2m_open "Polynomial P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_comp_eq_of_ker_le_of_separable.Polynomial"

namespace Polynomial
p2m_export "Polynomial" "C X natDegree_derivative_le coeff_natDegree eval_mul map_evalRingHom_eval coeff_map derivative_map evalEval_pow coeff natDegree_sub_eq_left_of_natDegree_lt aeval evalEval_C evalEval_sub degree IsRoot.def map_map coeff_sub map_C C_injective map one_lt_rootMultiplicity_iff_isRoot mem_roots evalRingHom degree_map_eq_of_injective count_roots evalEval_X Monic comp roots natDegree_modByMonic_le degree_C_le coe_mapRingHom rootMultiplicity_pos map_modByMonic sub_modByMonic coeff_zero natDegree eq_X_add_C_of_natDegree_le_one eq_C_of_natDegree_eq_zero eval_C finite_setOf_isRoot wronskian rootMultiplicity degree_mul_le evalEvalRingHom eval_sub degree_le_natDegree natDegree_modByMonic_lt derivative map_X modByMonic_add_div coeff_smul coeff_mul_add_eq_of_natDegree_le degree_map modByMonic_eq_zero_iff_dvd evalEval eval_map_algebraMap smul_modByMonic ext mapRingHom degree_eq_natDegree IsRoot natDegree_map_le degree_map_le natDegree_one ring lifts evalEval_mul coeff_derivative leadingCoeff_ne_zero eval natDegree_C_mul_le natDegree_map_eq_of_injective eval_smul"
namespace SepFibreDescent
p2m_open "Polynomial"

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k]

noncomputable def pencil (Φ S : F[X]) : F[X][X] := Φ.map C - C X * S.map C

noncomputable def fibrePoly (Φ S : F[X]) (x' : k) : k[X] :=
  Φ.map (algebraMap F k) - C x' * S.map (algebraMap F k)

theorem aeval_toRingHom_comp_C (x' : k) :
    ((aeval x' : F[X] →ₐ[F] k) : F[X] →+* k).comp C = algebraMap F k := by
  ext a
  simp

theorem map_map_C (p : F[X]) (x' : k) :
    (p.map C).map ((aeval x' : F[X] →ₐ[F] k) : F[X] →+* k) = p.map (algebraMap F k) := by
  rw [Polynomial.map_map, aeval_toRingHom_comp_C]

theorem pencil_map (Φ S : F[X]) (x' : k) :
    (pencil Φ S).map ((aeval x' : F[X] →ₐ[F] k) : F[X] →+* k) = fibrePoly Φ S x' := by
  simp only [pencil, fibrePoly, Polynomial.map_sub, Polynomial.map_mul, map_C, map_map_C]
  simp

theorem monic_pencil {Φ S : F[X]} (hΦ : Φ.Monic) (hdeg : Φ.natDegree = S.natDegree + 1) :
    (pencil Φ S).Monic := by
  unfold pencil
  refine (hΦ.map C).sub_of_left ?_
  calc (C X * S.map C).degree ≤ (C X : F[X][X]).degree + (S.map C).degree := degree_mul_le _ _
    _ ≤ 0 + (S.natDegree : WithBot ℕ) := by
        gcongr
        · exact degree_C_le
        · exact (degree_map_le).trans degree_le_natDegree
    _ < (Φ.map C).degree := by
        rw [zero_add, degree_map_eq_of_injective (C_injective), degree_eq_natDegree hΦ.ne_zero,
          hdeg]
        exact_mod_cast Nat.lt_succ_self _

theorem monic_fibrePoly {Φ S : F[X]} (hΦ : Φ.Monic) (hdeg : Φ.natDegree = S.natDegree + 1)
    (x' : k) : (fibrePoly Φ S x').Monic := by
  rw [← pencil_map]
  exact (monic_pencil hΦ hdeg).map _

theorem eval_fibrePoly (Φ S : F[X]) (x' ξ : k) :
    (fibrePoly Φ S x').eval ξ = aeval ξ Φ - x' * aeval ξ S := by
  simp [fibrePoly]

theorem aeval_S_ne_zero_of_isRoot {Φ S : F[X]} (hcop : IsCoprime Φ S) {x' ξ : k}
    (hξ : (fibrePoly Φ S x').IsRoot ξ) : aeval ξ S ≠ 0 := by
  intro hS
  rw [IsRoot, eval_fibrePoly, hS, mul_zero, sub_zero] at hξ
  obtain ⟨u, v, huv⟩ := hcop
  have := congrArg (aeval ξ) huv
  simp [hξ, hS] at this

theorem div_eq_of_isRoot {Φ S : F[X]} (hcop : IsCoprime Φ S) {x' ξ : k}
    (hξ : (fibrePoly Φ S x').IsRoot ξ) : aeval ξ Φ / aeval ξ S = x' := by
  have hS := aeval_S_ne_zero_of_isRoot hcop hξ
  rw [IsRoot, eval_fibrePoly, sub_eq_zero] at hξ
  rw [div_eq_iff hS, hξ]

theorem isRoot_of_div_eq {Φ S : F[X]} {x' ξ : k} (hS : aeval ξ S ≠ 0)
    (h : aeval ξ Φ / aeval ξ S = x') : (fibrePoly Φ S x').IsRoot ξ := by
  rw [IsRoot, eval_fibrePoly, sub_eq_zero]
  rw [div_eq_iff hS] at h
  exact h

noncomputable def wronskian (Φ S : F[X]) : F[X] := Φ * derivative S - derivative Φ * S

theorem wronskian_ne_zero {Φ S : F[X]} (hΦ : Φ.Monic) (hdeg : Φ.natDegree = S.natDegree + 1)
    (hS0 : S ≠ 0) : wronskian Φ S ≠ 0 := by
  intro h
  set d := Φ.natDegree with hd
  have hlc : Φ.coeff d = 1 := hΦ.coeff_natDegree
  have hSlc : S.coeff (d - 1) ≠ 0 := by
    have : d - 1 = S.natDegree := by omega
    rw [this]
    exact leadingCoeff_ne_zero.mpr hS0

  have h1 : (Φ * derivative S).coeff (d + (d - 2)) = Φ.coeff d * (derivative S).coeff (d - 2) :=
    coeff_mul_add_eq_of_natDegree_le le_rfl ((natDegree_derivative_le S).trans (by omega))
  have h2 : (derivative Φ * S).coeff ((d - 1) + (d - 1)) =
      (derivative Φ).coeff (d - 1) * S.coeff (d - 1) :=
    coeff_mul_add_eq_of_natDegree_le ((natDegree_derivative_le Φ).trans (by omega)) (by omega)
  rcases Nat.lt_or_ge d 2 with hd2 | hd2
  ·
    have hd1 : d = 1 := by omega
    have hSdeg : S.natDegree = 0 := by omega
    have hΦ' : derivative Φ = 1 := by
      have hΦeq : Φ = X + C (Φ.coeff 0) := by
        have := hΦ.eq_X_add_C (by omega : Φ.natDegree = 1)
        exact this
      rw [hΦeq]; simp
    have hS' : derivative S = 0 := by
      rw [eq_C_of_natDegree_eq_zero hSdeg]; simp
    apply hS0
    have : wronskian Φ S = -S := by rw [wronskian, hΦ', hS']; ring
    rw [this] at h
    exact neg_eq_zero.mp h
  · have hidx : (d - 1) + (d - 1) = d + (d - 2) := by omega
    rw [hidx] at h2
    have hc := congrArg (fun p : F[X] => p.coeff (d + (d - 2))) h
    simp only [wronskian, coeff_sub, coeff_zero, h1, h2, hlc, one_mul, coeff_derivative] at hc
    have e1 : d - 2 + 1 = d - 1 := by omega
    have e2 : d - 1 + 1 = d := by omega
    rw [e1, e2, hlc, one_mul] at hc
    apply hSlc
    have : S.coeff (d - 1) * ((↑(d - 2) + 1 : F) - (↑(d - 1) + 1)) = 0 := by
      linear_combination hc
    rw [mul_eq_zero] at this
    rcases this with h0 | h0
    · exact h0
    · exfalso
      have : ((↑(d - 2) + 1 : F) - (↑(d - 1) + 1)) = -1 := by
        have e3 : ((d - 1 : ℕ) : F) = ((d - 2 : ℕ) : F) + 1 := by
          rw [show d - 1 = (d - 2) + 1 by omega]; push_cast; ring
        rw [e3]; ring
      rw [this] at h0
      exact one_ne_zero (neg_eq_zero.mp h0)

theorem isRoot_wronskian_of_rootMultiplicity {Φ S : F[X]} (hcop : IsCoprime Φ S) {x' ξ : k}
    (hne : fibrePoly Φ S x' ≠ 0) (hm : 1 < (fibrePoly Φ S x').rootMultiplicity ξ) :
    aeval ξ (wronskian Φ S) = 0 := by
  rw [one_lt_rootMultiplicity_iff_isRoot hne] at hm
  obtain ⟨h0, h1⟩ := hm
  have hS := aeval_S_ne_zero_of_isRoot hcop h0
  rw [IsRoot, eval_fibrePoly, sub_eq_zero] at h0
  have h1' : aeval ξ (derivative Φ) - x' * aeval ξ (derivative S) = 0 := by
    have := h1
    rw [IsRoot] at this
    simpa [fibrePoly, derivative_map] using this
  simp only [wronskian, map_sub, map_mul]
  rw [sub_eq_zero] at h1'
  rw [h0, h1']
  ring

theorem nodup_roots_fibrePoly {Φ S : F[X]} (hcop : IsCoprime Φ S) {x' : k}
    (hne : fibrePoly Φ S x' ≠ 0)
    (hW : ∀ ξ : k, (fibrePoly Φ S x').IsRoot ξ → aeval ξ (wronskian Φ S) ≠ 0) :
    (fibrePoly Φ S x').roots.Nodup := by
  classical
  rw [Multiset.nodup_iff_count_le_one]
  intro ξ
  rw [count_roots]
  by_contra hlt
  push Not at hlt
  have hroot : (fibrePoly Φ S x').IsRoot ξ := by
    rw [← rootMultiplicity_pos hne]; omega
  exact hW ξ hroot (isRoot_wronskian_of_rootMultiplicity hcop hne hlt)

theorem fibrePoly_dvd [IsAlgClosed k] {Φ S : F[X]} {x' : k} (hne : fibrePoly Φ S x' ≠ 0)
    (hnodup : (fibrePoly Φ S x').roots.Nodup) {P : k[X]}
    (hP : ∀ ξ : k, (fibrePoly Φ S x').IsRoot ξ → P.IsRoot ξ) : fibrePoly Φ S x' ∣ P := by
  by_cases hP0 : P = 0
  · rw [hP0]; exact dvd_zero _
  rw [IsAlgClosed.dvd_iff_roots_le_roots hne hP0, Multiset.le_iff_subset hnodup]
  intro ξ hξ
  rw [mem_roots hP0]
  exact hP ξ ((mem_roots hne).mp hξ)

noncomputable def red (Φ S a : F[X]) : F[X][X] := (a.map C) %ₘ pencil Φ S

theorem red_map {Φ S : F[X]} (hΦ : Φ.Monic) (hdeg : Φ.natDegree = S.natDegree + 1) (a : F[X])
    (x' : k) : (red Φ S a).map ((aeval x' : F[X] →ₐ[F] k) : F[X] →+* k) =
      (a.map (algebraMap F k)) %ₘ fibrePoly Φ S x' := by
  rw [red, map_modByMonic _ (monic_pencil hΦ hdeg), map_map_C, pencil_map]

theorem aeval_coeff_red {Φ S : F[X]} (hΦ : Φ.Monic) (hdeg : Φ.natDegree = S.natDegree + 1)
    (a : F[X]) (x' : k) (i : ℕ) :
    aeval x' ((red Φ S a).coeff i) = ((a.map (algebraMap F k)) %ₘ fibrePoly Φ S x').coeff i := by
  rw [← red_map hΦ hdeg, coeff_map]
  rfl

theorem descent [IsAlgClosed k]
    {Φ S : F[X]} (hΦ : Φ.Monic) (hdeg : Φ.natDegree = S.natDegree + 1) (hcop : IsCoprime Φ S)
    {a b : F[X]} {G T : Set k} (hG : G.Finite) (hT : T.Finite)
    (hS : ∀ ξ ∉ G, aeval ξ S ≠ 0) (hb : ∀ ξ ∉ G, aeval ξ b ≠ 0)
    (hconst : ∀ ξ₁ ∉ G, ∀ ξ₂ ∉ G, aeval ξ₁ Φ / aeval ξ₁ S ∉ T →
      aeval ξ₁ Φ / aeval ξ₁ S = aeval ξ₂ Φ / aeval ξ₂ S →
      aeval ξ₁ a / aeval ξ₁ b = aeval ξ₂ a / aeval ξ₂ b) :
    ∃ (c e : F[X]) (T' : Set k), T'.Finite ∧ ∀ x' ∉ T', aeval x' e ≠ 0 ∧
      ∀ ξ ∉ G, aeval ξ Φ / aeval ξ S = x' →
        aeval ξ a / aeval ξ b = aeval x' c / aeval x' e := by
  classical
  set θ : k → k := fun ξ => aeval ξ Φ / aeval ξ S with hθ

  obtain ⟨ξ₀, hξ₀⟩ := hG.infinite_compl.nonempty
  have hξ₀G : ξ₀ ∉ G := hξ₀
  have hS0 : S ≠ 0 := by
    intro h; exact hS ξ₀ hξ₀G (by simp [h])

  have hredb : red Φ S b ≠ 0 := by
    intro h0
    have h1 := red_map (k := k) hΦ hdeg b (θ ξ₀)
    rw [h0, Polynomial.map_zero, eq_comm, modByMonic_eq_zero_iff_dvd (monic_fibrePoly hΦ hdeg _)]
      at h1
    have hroot : (fibrePoly Φ S (θ ξ₀)).IsRoot ξ₀ := isRoot_of_div_eq (hS ξ₀ hξ₀G) rfl
    have := hroot.dvd h1
    rw [IsRoot, eval_map_algebraMap] at this
    exact hb ξ₀ hξ₀G this
  set i := (red Φ S b).natDegree
  refine ⟨(red Φ S a).coeff i, (red Φ S b).coeff i,
    T ∪ θ '' (G ∪ {ξ | aeval ξ (wronskian Φ S) = 0}) ∪
      {x' | aeval x' ((red Φ S b).coeff i) = 0}, ?_, ?_⟩
  · refine ((hT.union ((hG.union ?_).image θ)).union ?_)
    · have h := (wronskian_ne_zero hΦ hdeg hS0)
      have : {ξ : k | aeval ξ (wronskian Φ S) = 0} =
          {ξ | ((wronskian Φ S).map (algebraMap F k)).IsRoot ξ} := by
        ext ξ; simp [IsRoot]
      rw [this]
      exact finite_setOf_isRoot ((Polynomial.map_ne_zero_iff (algebraMap F k).injective).mpr h)
    · have h : (red Φ S b).coeff i ≠ 0 := leadingCoeff_ne_zero.mpr hredb
      have : {x' : k | aeval x' ((red Φ S b).coeff i) = 0} =
          {x' | (((red Φ S b).coeff i).map (algebraMap F k)).IsRoot x'} := by
        ext ξ; simp [IsRoot]
      rw [this]
      exact finite_setOf_isRoot ((Polynomial.map_ne_zero_iff (algebraMap F k).injective).mpr h)
  intro x' hx'
  simp only [Set.mem_union, Set.mem_image, Set.mem_setOf_eq, not_or, not_exists, not_and] at hx'
  obtain ⟨⟨hxT, hximg⟩, hxe⟩ := hx'
  refine ⟨hxe, fun ξ hξG hξx => ?_⟩
  set m := fibrePoly Φ S x' with hm
  have hmne : m ≠ 0 := (monic_fibrePoly hΦ hdeg x').ne_zero

  have hrootG : ∀ ξ' : k, m.IsRoot ξ' → ξ' ∉ G := by
    intro ξ' hξ' hG'
    exact hximg ξ' (Or.inl hG') (div_eq_of_isRoot hcop hξ')
  have hrootW : ∀ ξ' : k, m.IsRoot ξ' → aeval ξ' (wronskian Φ S) ≠ 0 := by
    intro ξ' hξ' hW
    exact hximg ξ' (Or.inr hW) (div_eq_of_isRoot hcop hξ')
  have hnodup : m.roots.Nodup := nodup_roots_fibrePoly hcop hmne hrootW
  set h : k := aeval ξ a / aeval ξ b with hh

  have hvan : ∀ ξ' : k, m.IsRoot ξ' →
      (a.map (algebraMap F k) - h • b.map (algebraMap F k)).IsRoot ξ' := by
    intro ξ' hξ'
    have hξ'G := hrootG ξ' hξ'
    have hθ' : θ ξ' = x' := div_eq_of_isRoot hcop hξ'
    have hθ'' : aeval ξ' Φ / aeval ξ' S = x' := hθ'
    have hc := hconst ξ' hξ'G ξ hξG (by rw [hθ'']; exact hxT) (by rw [hθ'']; exact hξx.symm)
    have hbξ' := hb ξ' hξ'G
    rw [IsRoot, eval_sub, eval_smul, eval_map_algebraMap, eval_map_algebraMap, smul_eq_mul]
    have : h = aeval ξ' a / aeval ξ' b := by rw [hh, hc]
    rw [this, div_mul_cancel₀ _ hbξ', sub_self]
  have hdvd : m ∣ a.map (algebraMap F k) - h • b.map (algebraMap F k) :=
    fibrePoly_dvd hmne hnodup hvan
  rw [← modByMonic_eq_zero_iff_dvd (monic_fibrePoly hΦ hdeg x'), sub_modByMonic,
    smul_modByMonic, sub_eq_zero] at hdvd
  have hci := congrArg (fun p : k[X] => p.coeff i) hdvd
  simp only [coeff_smul, smul_eq_mul] at hci
  rw [← hm, ← aeval_coeff_red hΦ hdeg, ← aeval_coeff_red hΦ hdeg] at hci
  rw [hci, mul_div_assoc, div_self hxe, mul_one]

end Polynomial.SepFibreDescent

p2m_open "Polynomial P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_comp_eq_of_ker_le_of_separable.Polynomial"
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY Affine.Y_eq_of_Y_ne Affine.equation_neg a₃ map_map a₁ map Affine.CoordinateRing mk Ψ₂Sq a₄ a₂ a₆ Affine.Point.some Affine.CoordinateRing.mk_ψ₂_sq Affine.degree_polynomial Affine.Point.some.inj Affine.map_polynomial toAffine Affine.Point Affine.CoordinateRing.mk Affine.evalEval_polynomialY Affine.natDegree_polynomial ψ₂ Affine.nonsingular_neg Affine.monic_polynomial Affine.Point.some_ne_zero c₄ Affine.equation_iff Affine.Point.neg_some map_Ψ₂Sq baseChange evalEvalBC IsRationallyRepresented rationalHomSet surjective_of_mem_rationalHomSet Psi2Sq_ne_zero_of_isElliptic"
namespace SepIsogFactor
p2m_open "WeierstrassCurve"

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k]

noncomputable def bc (x y : k) : F[X][Y] →+* k :=
  (evalEvalRingHom x y).comp (mapRingHom (mapRingHom (algebraMap F k)))

theorem bc_apply (p : F[X][Y]) (x y : k) :
    bc x y p = (p.map (mapRingHom (algebraMap F k))).evalEval x y := by
  simp [bc]

theorem evalEvalBC_eq_bc (p : F[X][Y]) (x y : k) : evalEvalBC k p x y = bc x y p := by
  rw [bc_apply]; rfl

@[scoped simp] theorem bc_C (p : F[X]) (x y : k) : bc x y (C p) = aeval x p := by
  rw [bc_apply, Polynomial.map_C, evalEval_C, coe_mapRingHom, eval_map_algebraMap]

@[scoped simp] theorem bc_X (x y : k) : bc x y (Y : F[X][Y]) = y := by
  rw [bc_apply, Polynomial.map_X, evalEval_X]

variable (W : WeierstrassCurve F)

theorem bc_polynomial {x y : k} (h : (W.baseChange k).toAffine.Equation x y) :
    bc x y W.toAffine.polynomial = 0 := by
  rw [bc_apply, ← WeierstrassCurve.Affine.map_polynomial]
  exact h

theorem exists_linear (p : F[X][Y]) : ∃ p₀ p₁ : F[X], ∀ (x y : k),
    (W.baseChange k).toAffine.Equation x y → bc x y p = aeval x p₀ + aeval x p₁ * y := by
  have hf : W.toAffine.polynomial.Monic := WeierstrassCurve.Affine.monic_polynomial
  have hr : (p %ₘ W.toAffine.polynomial).natDegree ≤ 1 := by
    have h2 : W.toAffine.polynomial.natDegree = 2 := WeierstrassCurve.Affine.natDegree_polynomial
    have := natDegree_modByMonic_le p hf
    have := natDegree_modByMonic_lt p hf
      (ne_of_apply_ne natDegree (by rw [h2, natDegree_one]; decide))
    omega
  refine ⟨(p %ₘ W.toAffine.polynomial).coeff 0, (p %ₘ W.toAffine.polynomial).coeff 1,
    fun x y hxy => ?_⟩
  have hp : bc x y p = bc x y (W.toAffine.polynomial * (p /ₘ W.toAffine.polynomial)) +
      bc x y (p %ₘ W.toAffine.polynomial) := by
    rw [← map_add, add_comm, modByMonic_add_div]
  have hr' : bc x y (p %ₘ W.toAffine.polynomial) = aeval x ((p %ₘ W.toAffine.polynomial).coeff 0) +
      aeval x ((p %ₘ W.toAffine.polynomial).coeff 1) * y := by
    conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hr]
    rw [map_add, map_mul, bc_C, bc_C, bc_X]
    ring
  rw [hp, map_mul, bc_polynomial W hxy, zero_mul, zero_add, hr']

noncomputable def linPoly : F[X] := C W.a₁ * X + C W.a₃

noncomputable def rhsPoly : F[X] := X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆

noncomputable def cj₀ (n₀ n₁ d₀ d₁ : F[X]) : F[X] :=
  n₀ * d₀ - linPoly W * n₀ * d₁ - rhsPoly W * n₁ * d₁

noncomputable def cj₁ (n₀ n₁ d₀ d₁ : F[X]) : F[X] := n₁ * d₀ - n₀ * d₁

theorem negY_eq (x y : k) : (W.baseChange k).toAffine.negY x y = -y - aeval x (linPoly W) := by
  simp [WeierstrassCurve.Affine.negY, linPoly]
  ring

theorem equation_iff_aeval (x y : k) : (W.baseChange k).toAffine.Equation x y ↔
    y ^ 2 + aeval x (linPoly W) * y = aeval x (rhsPoly W) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [linPoly, rhsPoly]
  constructor <;> intro h <;> linear_combination h

theorem conj_mul {x y : k} (h : (W.baseChange k).toAffine.Equation x y) (n₀ n₁ d₀ d₁ : F[X]) :
    (aeval x n₀ + aeval x n₁ * y) * (aeval x d₀ + aeval x d₁ * (W.baseChange k).toAffine.negY x y) =
      aeval x (cj₀ W n₀ n₁ d₀ d₁) + aeval x (cj₁ n₀ n₁ d₀ d₁) * y := by
  rw [equation_iff_aeval] at h
  simp only [negY_eq, cj₀, cj₁, map_sub, map_mul]
  linear_combination (-(aeval x n₁ * aeval x d₁)) * h

theorem exists_ratio_linear (n d : F[X][Y]) : ∃ p₀ p₁ q : F[X], ∀ (x y : k),
    (W.baseChange k).toAffine.Equation x y → bc x y d ≠ 0 →
      bc x ((W.baseChange k).toAffine.negY x y) d ≠ 0 →
        aeval x q ≠ 0 ∧ bc x y n / bc x y d = (aeval x p₀ + aeval x p₁ * y) / aeval x q := by
  obtain ⟨n₀, n₁, hn⟩ := exists_linear (k := k) W n
  obtain ⟨d₀, d₁, hd⟩ := exists_linear (k := k) W d
  refine ⟨cj₀ W n₀ n₁ d₀ d₁, cj₁ n₀ n₁ d₀ d₁, cj₀ W d₀ d₁ d₀ d₁, fun x y hxy hd1 hd2 => ?_⟩
  have hxy' : (W.baseChange k).toAffine.Equation x ((W.baseChange k).toAffine.negY x y) :=
    (WeierstrassCurve.Affine.equation_neg x y).mpr hxy
  rw [hd x _ hxy'] at hd2
  rw [hd x y hxy] at hd1
  rw [hn x y hxy, hd x y hxy]
  have hq : aeval x (cj₀ W d₀ d₁ d₀ d₁) = (aeval x d₀ + aeval x d₁ * y) *
      (aeval x d₀ + aeval x d₁ * (W.baseChange k).toAffine.negY x y) := by
    rw [conj_mul W hxy, show cj₁ d₀ d₁ d₀ d₁ = 0 from by unfold cj₁; ring, map_zero, zero_mul,
      add_zero]
  refine ⟨by rw [hq]; exact mul_ne_zero hd1 hd2, ?_⟩
  rw [← conj_mul W hxy, hq, mul_comm (aeval x d₀ + aeval x d₁ * y) _, ← div_div,
    mul_div_cancel_right₀ _ hd2]

theorem evalEval_eq_of_mk_eq {W' : WeierstrassCurve k} {p q : k[X][Y]}
    (hpq : WeierstrassCurve.Affine.CoordinateRing.mk W' p =
      WeierstrassCurve.Affine.CoordinateRing.mk W' q)
    {x y : k} (h : W'.toAffine.Equation x y) : p.evalEval x y = q.evalEval x y := by
  rw [AdjoinRoot.mk_eq_mk] at hpq
  obtain ⟨r, hr⟩ := hpq
  have := congrArg (evalEval x y) hr
  rw [evalEval_sub, evalEval_mul, h, zero_mul, sub_eq_zero] at this
  exact this

scoped instance instIsEllipticBaseChange [W.IsElliptic] : (W.baseChange k).IsElliptic :=
  inferInstanceAs ((W.map (algebraMap F k)).IsElliptic)

theorem aeval_Ψ₂Sq_eq_zero {x y : k} (h : (W.baseChange k).toAffine.Equation x y)
    (hy : y = (W.baseChange k).toAffine.negY x y) : aeval x W.Ψ₂Sq = 0 := by
  have h1 := evalEval_eq_of_mk_eq
    (WeierstrassCurve.Affine.CoordinateRing.mk_ψ₂_sq (W := W.baseChange k)) h
  rw [evalEval_pow, evalEval_C, WeierstrassCurve.baseChange, WeierstrassCurve.map_Ψ₂Sq,
    eval_map_algebraMap] at h1
  rw [← WeierstrassCurve.baseChange] at h1
  rw [← h1, WeierstrassCurve.ψ₂, WeierstrassCurve.Affine.evalEval_polynomialY]
  have hu : 2 * y + (W.baseChange k).a₁ * x + (W.baseChange k).a₃ = 0 := by
    rw [WeierstrassCurve.Affine.negY] at hy
    linear_combination hy
  rw [hu, zero_pow two_ne_zero]

theorem finite_setOf_aeval_eq_zero {p : F[X]} (hp : p ≠ 0) : {x : k | aeval x p = 0}.Finite := by
  refine (finite_setOf_isRoot
    ((Polynomial.map_ne_zero_iff (algebraMap F k).injective).mpr hp)).subset ?_
  intro x hx
  simpa [IsRoot, eval_map_algebraMap] using hx

theorem monic_fibre {Φ S : F[X]} (hΦ : Φ.Monic) (hdeg : S.natDegree < Φ.natDegree) (r : k) :
    (Φ.map (algebraMap F k) - C r * S.map (algebraMap F k)).Monic := by
  refine (hΦ.map _).sub_of_left ?_
  calc (C r * S.map (algebraMap F k)).degree
        ≤ (C r).degree + (S.map (algebraMap F k)).degree := degree_mul_le _ _
    _ ≤ 0 + (S.natDegree : WithBot ℕ) := by
        gcongr
        · exact degree_C_le
        · exact (degree_map_le).trans degree_le_natDegree
    _ < (Φ.map (algebraMap F k)).degree := by
        rw [zero_add, degree_map_eq_of_injective (algebraMap F k).injective,
          degree_eq_natDegree hΦ.ne_zero]
        exact_mod_cast hdeg

theorem finite_fibre {Φ S : F[X]} (hΦ : Φ.Monic) (hdeg : S.natDegree < Φ.natDegree) (r : k) :
    {ξ : k | aeval ξ Φ = r * aeval ξ S}.Finite := by
  refine (finite_setOf_isRoot (monic_fibre hΦ hdeg r).ne_zero).subset ?_
  intro ξ hξ
  simp only [Set.mem_setOf_eq, IsRoot, eval_sub, eval_mul, eval_C, eval_map_algebraMap] at hξ ⊢
  rw [hξ, sub_self]

theorem exists_mem_fibre [IsAlgClosed k] {Φ S : F[X]} (hΦ : Φ.Monic)
    (hdeg : Φ.natDegree = S.natDegree + 1) (hcop : IsCoprime Φ S) (r : k) :
    ∃ ξ : k, aeval ξ S ≠ 0 ∧ aeval ξ Φ / aeval ξ S = r := by
  have hm := monic_fibre (k := k) hΦ (by omega : S.natDegree < Φ.natDegree) r
  have hdeg' : (Φ.map (algebraMap F k) - C r * S.map (algebraMap F k)).degree ≠ 0 := by
    rw [degree_eq_natDegree hm.ne_zero, natDegree_sub_eq_left_of_natDegree_lt,
      natDegree_map_eq_of_injective (algebraMap F k).injective]
    · exact_mod_cast (by omega : Φ.natDegree ≠ 0)
    · rw [natDegree_map_eq_of_injective (algebraMap F k).injective]
      calc (C r * S.map (algebraMap F k)).natDegree ≤ (S.map (algebraMap F k)).natDegree :=
            natDegree_C_mul_le _ _
        _ ≤ S.natDegree := natDegree_map_le
        _ < Φ.natDegree := by omega
  obtain ⟨ξ, hξ⟩ := IsAlgClosed.exists_root _ hdeg'
  simp only [IsRoot, eval_sub, eval_mul, eval_C, eval_map_algebraMap, sub_eq_zero] at hξ
  have hS : aeval ξ S ≠ 0 := by
    intro hS
    rw [hS, mul_zero] at hξ
    obtain ⟨u, v, huv⟩ := hcop
    have := congrArg (aeval ξ) huv
    simp [hξ, hS] at this
  exact ⟨ξ, hS, by rw [div_eq_iff hS, hξ]⟩

theorem exists_nonsingular [IsAlgClosed k] [W.IsElliptic] (x : k) :
    ∃ y : k, (W.baseChange k).toAffine.Nonsingular x y := by
  have hdeg : ((W.baseChange k).toAffine.polynomial.map (evalRingHom x)).degree ≠ 0 := by
    rw [WeierstrassCurve.Affine.monic_polynomial.degree_map,
      WeierstrassCurve.Affine.degree_polynomial]
    norm_num
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root _ hdeg
  refine ⟨y, ((W.baseChange k).toAffine.equation_iff_nonsingular).mp ?_⟩
  rw [IsRoot.def, map_evalRingHom_eval] at hy
  exact hy

section Shape

variable {W}
variable {W₂ : WeierstrassCurve F} [DecidableEq k]

def SepShape (φ : (W.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point)
    (P S N₀ N₁ R : F[X]) (B : Set k) : Prop :=
  ∀ (x y : k) (h : (W.baseChange k).toAffine.Nonsingular x y), x ∉ B →
    aeval x S ≠ 0 ∧ aeval x R ≠ 0 ∧
      ∃ h', φ (.some x y h) =
        .some (aeval x P / aeval x S) ((aeval x N₀ + aeval x N₁ * y) / aeval x R) h'

variable {φ : (W.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point}
  {P S N₀ N₁ R : F[X]} {B : Set k}

theorem phi_coords (hφ : SepShape φ P S N₀ N₁ R B) {ξ η : k}
    {h : (W.baseChange k).toAffine.Nonsingular ξ η} {x' y' : k}
    {h' : (W₂.baseChange k).toAffine.Nonsingular x' y'} (hξ : ξ ∉ B)
    (hn : φ (.some ξ η h) = .some x' y' h') :
    aeval ξ S ≠ 0 ∧ aeval ξ R ≠ 0 ∧ x' * aeval ξ S = aeval ξ P ∧
      y' * aeval ξ R = aeval ξ N₀ + aeval ξ N₁ * η := by
  obtain ⟨hS, hR, h'', e⟩ := hφ ξ η h hξ
  rw [hn] at e
  obtain ⟨hx, hy⟩ := WeierstrassCurve.Affine.Point.some.inj e
  refine ⟨hS, hR, ?_, ?_⟩
  · rw [hx, div_mul_cancel₀ _ hS]
  · rw [hy, div_mul_cancel₀ _ hR]

theorem phi_some_ne_zero (hφ : SepShape φ P S N₀ N₁ R B) {ξ η : k}
    (h : (W.baseChange k).toAffine.Nonsingular ξ η) (hξ : ξ ∉ B) : φ (.some ξ η h) ≠ 0 := by
  obtain ⟨-, -, h', e⟩ := hφ ξ η h hξ
  rw [e]
  exact WeierstrassCurve.Affine.Point.some_ne_zero h'

theorem mem_rationalHomSet_of_sepShape (hB : B.Finite) (hφ : SepShape φ P S N₀ N₁ R B) :
    φ ∈ rationalHomSet k W W₂ := by
  refine Or.inr ⟨C P, C S, C N₀ + C N₁ * Y, C R, B, hB, fun x y h hx => ?_⟩
  simp only [evalEvalBC_eq_bc, map_add, map_mul, bc_C, bc_X]
  exact hφ x y h hx

theorem ne_zero_of_sepShape [IsAlgClosed k] [W.IsElliptic] (hB : B.Finite)
    (hφ : SepShape φ P S N₀ N₁ R B) : φ ≠ 0 := by
  intro h0
  haveI : Infinite k := IsAlgClosed.instInfinite
  obtain ⟨x, hx⟩ := hB.infinite_compl.nonempty
  obtain ⟨y, hy⟩ := exists_nonsingular W x
  exact phi_some_ne_zero hφ hy hx (by rw [h0, AddMonoidHom.zero_apply])

theorem phi_neg {ξ η : k}
    {h : (W.baseChange k).toAffine.Nonsingular ξ η} {x' y' : k}
    {h' : (W₂.baseChange k).toAffine.Nonsingular x' y'}
    (hn : φ (.some ξ η h) = .some x' y' h') :
    φ (.some ξ ((W.baseChange k).toAffine.negY ξ η)
      ((WeierstrassCurve.Affine.nonsingular_neg ..).mpr h)) =
        .some x' ((W₂.baseChange k).toAffine.negY x' y')
          ((WeierstrassCurve.Affine.nonsingular_neg ..).mpr h') := by
  rw [← WeierstrassCurve.Affine.Point.neg_some h, map_neg, hn,
    WeierstrassCurve.Affine.Point.neg_some h']

theorem N₁_ne_zero [IsAlgClosed k] [W.IsElliptic] [W₂.IsElliptic] (hPm : P.Monic)
    (hdeg : P.natDegree = S.natDegree + 1) (hB : B.Finite) (hφ : SepShape φ P S N₀ N₁ R B) :
    N₁ ≠ 0 := by
  intro hN1
  subst hN1
  haveI : Infinite k := IsAlgClosed.instInfinite
  have hU : Bᶜ.Infinite := hB.infinite_compl
  have hT : {x' : k | aeval x' W₂.Ψ₂Sq = 0}.Finite :=
    finite_setOf_aeval_eq_zero (WeierstrassCurve.Psi2Sq_ne_zero_of_isElliptic W₂)
  have hlt : S.natDegree < P.natDegree := by omega
  refine hU ((hT.biUnion fun x' _ => finite_fibre (k := k) hPm hlt x').subset ?_)
  intro ξ hξ
  have hξB : ξ ∉ B := hξ
  obtain ⟨η, hη⟩ := exists_nonsingular W ξ
  rcases hQ : φ (Affine.Point.some ξ η hη) with _ | ⟨x₁, y₁, h₁⟩
  · exact absurd hQ (phi_some_ne_zero hφ hη hξB)
  obtain ⟨hS, hR, hx, hy⟩ := phi_coords hφ hξB hQ
  obtain ⟨-, -, -, hy'⟩ := phi_coords hφ hξB (phi_neg hQ)
  simp only [map_zero, zero_mul, add_zero] at hy hy'
  refine Set.mem_iUnion₂.mpr ⟨x₁, aeval_Ψ₂Sq_eq_zero W₂ h₁.left ?_, ?_⟩
  · exact mul_right_cancel₀ hR (hy.trans hy'.symm)
  · simp only [Set.mem_setOf_eq]
    exact hx.symm

theorem exists_lift [IsAlgClosed k] [W.IsElliptic] (hφ : SepShape φ P S N₀ N₁ R B) {ξ : k}
    (hξ : ξ ∉ B) {x' y' : k} (h' : (W₂.baseChange k).toAffine.Nonsingular x' y')
    (hx : x' * aeval ξ S = aeval ξ P) :
    ∃ (η : k) (h : (W.baseChange k).toAffine.Nonsingular ξ η),
      φ (Affine.Point.some ξ η h) = .some x' y' h' := by
  obtain ⟨η₀, hη₀⟩ := exists_nonsingular W ξ
  rcases hQ : φ (Affine.Point.some ξ η₀ hη₀) with _ | ⟨x₀, y₀, h₀⟩
  · exact absurd hQ (phi_some_ne_zero hφ hη₀ hξ)
  obtain ⟨hS, -, hx₀, -⟩ := phi_coords hφ hξ hQ
  have hx0 : x₀ = x' := mul_right_cancel₀ hS (by rw [hx₀, hx])
  subst hx0
  by_cases hy : y' = (W₂.baseChange k).toAffine.negY x₀ y₀
  · refine ⟨_, (WeierstrassCurve.Affine.nonsingular_neg ..).mpr hη₀, ?_⟩
    rw [phi_neg hQ]
    subst hy
    rfl
  · have := WeierstrassCurve.Affine.Y_eq_of_Y_ne h'.left h₀.left rfl hy
    subst this
    exact ⟨η₀, hη₀, hQ⟩

end Shape

theorem exists_hom_of_ker {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (φ : A →+ B) (hsurj : Function.Surjective φ) (α : A →+ C)
    (hker : ∀ P, φ P = 0 → α P = 0) : ∃ β : B →+ C, ∀ Q, β (φ Q) = α Q := by
  choose f hf using hsurj
  have key : ∀ P Q : A, φ P = φ Q → α P = α Q := fun P Q h => by
    rw [← sub_eq_zero, ← map_sub]
    exact hker _ (by rw [map_sub, h, sub_self])
  refine ⟨{ toFun := fun P => α (f P), map_zero' := ?_, map_add' := ?_ }, ?_⟩
  · simpa using key (f 0) 0 (by rw [hf, map_zero])
  · intro P Q
    simp only [← map_add]
    exact key _ _ (by rw [hf, map_add, hf, hf])
  · intro Q
    exact key _ _ (hf _)

section Fibre

variable {W}
variable [IsAlgClosed k] [DecidableEq k] [W.IsElliptic] {W₂ W₃ : WeierstrassCurve F}
  [W₂.IsElliptic]

def CoordSpec (α : (W.baseChange k).toAffine.Point →+ (W₃.baseChange k).toAffine.Point)
    (crd : (W₃.baseChange k).toAffine.Point → k) (Bα : Set k) (p₀ p₁ q : F[X]) : Prop :=
  ∀ (ξ η : k) (h : (W.baseChange k).toAffine.Nonsingular ξ η), ξ ∉ Bα →
    aeval ξ q ≠ 0 ∧ crd (α (.some ξ η h)) = (aeval ξ p₀ + aeval ξ p₁ * η) / aeval ξ q

variable {α : (W.baseChange k).toAffine.Point →+ (W₃.baseChange k).toAffine.Point}
  {crd : (W₃.baseChange k).toAffine.Point → k} {Bα : Set k} {p₀ p₁ q : F[X]}
  {φ : (W.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point}
  {P S N₀ N₁ R : F[X]} {B : Set k}

omit [IsAlgClosed k] [W.IsElliptic] [W₂.IsElliptic] in

theorem coord_formula (hc : CoordSpec α crd Bα p₀ p₁ q) (hφ : SepShape φ P S N₀ N₁ R B)
    {ξ η : k} {h : (W.baseChange k).toAffine.Nonsingular ξ η} {x' y' : k}
    {h' : (W₂.baseChange k).toAffine.Nonsingular x' y'} (hBα : ξ ∉ Bα) (hB : ξ ∉ B)
    (hN1 : aeval ξ N₁ ≠ 0) (hn : φ (Affine.Point.some ξ η h) = .some x' y' h') :
    aeval ξ (q * N₁) ≠ 0 ∧ crd (α (.some ξ η h)) =
      aeval ξ (p₀ * N₁ - p₁ * N₀) / aeval ξ (q * N₁) +
        aeval ξ (p₁ * R) / aeval ξ (q * N₁) * y' := by
  obtain ⟨hq, hcrd⟩ := hc ξ η h hBα
  obtain ⟨-, hR, -, hy⟩ := phi_coords hφ hB hn
  refine ⟨by rw [map_mul]; exact mul_ne_zero hq hN1, ?_⟩
  rw [hcrd]
  have hη : η = (y' * aeval ξ R - aeval ξ N₀) / aeval ξ N₁ := by
    rw [eq_div_iff hN1]
    linear_combination -hy
  rw [hη]
  simp only [map_mul, map_sub]
  field_simp
  ring

theorem fibre_const (hker : ∀ T, φ T = 0 → α T = 0)
    (hc : CoordSpec α crd Bα p₀ p₁ q) (hφ : SepShape φ P S N₀ N₁ R B)
    {ξ₁ ξ₂ : k} (hBα₁ : ξ₁ ∉ Bα) (hB₁ : ξ₁ ∉ B) (hN₁ : aeval ξ₁ N₁ ≠ 0)
    (hBα₂ : ξ₂ ∉ Bα) (hB₂ : ξ₂ ∉ B) (hN₂ : aeval ξ₂ N₁ ≠ 0) {x' : k}
    (hx₁ : x' * aeval ξ₁ S = aeval ξ₁ P) (hx₂ : x' * aeval ξ₂ S = aeval ξ₂ P)
    (hT : aeval x' W₂.Ψ₂Sq ≠ 0) :
    aeval ξ₁ (p₀ * N₁ - p₁ * N₀) / aeval ξ₁ (q * N₁) =
        aeval ξ₂ (p₀ * N₁ - p₁ * N₀) / aeval ξ₂ (q * N₁) ∧
      aeval ξ₁ (p₁ * R) / aeval ξ₁ (q * N₁) = aeval ξ₂ (p₁ * R) / aeval ξ₂ (q * N₁) := by
  obtain ⟨y', h'⟩ := exists_nonsingular W₂ x'
  obtain ⟨η₁, h₁, hn₁⟩ := exists_lift hφ hB₁ h' hx₁
  obtain ⟨η₂, h₂, hn₂⟩ := exists_lift hφ hB₂ h' hx₂
  have hα : α (.some ξ₁ η₁ h₁) = α (.some ξ₂ η₂ h₂) := by
    rw [← sub_eq_zero, ← map_sub]
    exact hker _ (by rw [map_sub, hn₁, hn₂, sub_self])
  have hn₁' := phi_neg hn₁
  have hn₂' := phi_neg hn₂
  have hα' : α (.some ξ₁ ((W.baseChange k).toAffine.negY ξ₁ η₁)
      ((WeierstrassCurve.Affine.nonsingular_neg ..).mpr h₁)) =
        α (.some ξ₂ ((W.baseChange k).toAffine.negY ξ₂ η₂)
          ((WeierstrassCurve.Affine.nonsingular_neg ..).mpr h₂)) := by
    rw [← WeierstrassCurve.Affine.Point.neg_some h₁, ← WeierstrassCurve.Affine.Point.neg_some h₂,
      map_neg, map_neg, hα]
  obtain ⟨-, e₁⟩ := coord_formula hc hφ hBα₁ hB₁ hN₁ hn₁
  obtain ⟨-, e₂⟩ := coord_formula hc hφ hBα₂ hB₂ hN₂ hn₂
  obtain ⟨-, e₁'⟩ := coord_formula hc hφ hBα₁ hB₁ hN₁ hn₁'
  obtain ⟨-, e₂'⟩ := coord_formula hc hφ hBα₂ hB₂ hN₂ hn₂'
  have E := congrArg crd hα
  have E' := congrArg crd hα'
  rw [e₁, e₂] at E
  rw [e₁', e₂'] at E'
  have hy : y' - (W₂.baseChange k).toAffine.negY x' y' ≠ 0 := by
    intro heq
    exact hT (aeval_Ψ₂Sq_eq_zero W₂ h'.left (sub_eq_zero.mp heq))
  have hA' : aeval ξ₁ (p₁ * R) / aeval ξ₁ (q * N₁) =
      aeval ξ₂ (p₁ * R) / aeval ξ₂ (q * N₁) := by
    refine mul_right_cancel₀ hy ?_
    linear_combination E - E'
  exact ⟨by linear_combination E - y' * hA', hA'⟩

end Fibre

section Assembly

variable {W}
variable [IsAlgClosed k] [DecidableEq k] [W.IsElliptic] {W₂ W₃ : WeierstrassCurve F}
  [W₂.IsElliptic]
variable {α : (W.baseChange k).toAffine.Point →+ (W₃.baseChange k).toAffine.Point}
  {crd : (W₃.baseChange k).toAffine.Point → k} {Bα : Set k} {p₀ p₁ q : F[X]}
  {φ : (W.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point}
  {P S N₀ N₁ R : F[X]} {B : Set k}

def bad (Bα B : Set k) (N₁ : F[X]) : Set k := Bα ∪ B ∪ {ξ | aeval ξ N₁ = 0}

omit [IsAlgClosed k] [DecidableEq k] [W.IsElliptic] [W₂.IsElliptic] in
theorem finite_bad (hBα : Bα.Finite) (hB : B.Finite) (hN1 : N₁ ≠ 0) :
    (bad (k := k) Bα B N₁).Finite :=
  (hBα.union hB).union (finite_setOf_aeval_eq_zero hN1)

omit [IsAlgClosed k] [DecidableEq k] [W.IsElliptic] [W₂.IsElliptic] in
theorem not_mem_bad {ξ : k} :
    ξ ∉ bad (k := k) Bα B N₁ ↔ ξ ∉ Bα ∧ ξ ∉ B ∧ aeval ξ N₁ ≠ 0 := by
  simp only [bad, Set.mem_union, Set.mem_setOf_eq, not_or, and_assoc]

theorem descent_pair (hPm : P.Monic) (hdeg : P.natDegree = S.natDegree + 1)
    (hcop : IsCoprime P S) (hker : ∀ T, φ T = 0 → α T = 0)
    (hc : CoordSpec α crd Bα p₀ p₁ q) (hφ : SepShape φ P S N₀ N₁ R B) (hN1 : N₁ ≠ 0)
    (hBα : Bα.Finite) (hB : B.Finite) :
    ∃ (c e c' e' : F[X]) (T' : Set k), T'.Finite ∧ ∀ x' ∉ T', aeval x' e ≠ 0 ∧
      aeval x' e' ≠ 0 ∧ ∀ ξ ∉ bad Bα B N₁, ∀ (η : k)
        (h : (W.baseChange k).toAffine.Nonsingular ξ η) (y' : k)
        (h' : (W₂.baseChange k).toAffine.Nonsingular x' y'),
        φ (Affine.Point.some ξ η h) = .some x' y' h' →
          crd (α (.some ξ η h)) = aeval x' c / aeval x' e + aeval x' c' / aeval x' e' * y' := by
  have hG := finite_bad (k := k) hBα hB hN1
  have hT : {x' : k | aeval x' W₂.Ψ₂Sq = 0}.Finite :=
    finite_setOf_aeval_eq_zero (WeierstrassCurve.Psi2Sq_ne_zero_of_isElliptic W₂)
  have hS' : ∀ ξ ∉ bad Bα B N₁, aeval ξ S ≠ 0 := fun ξ hξ => by
    obtain ⟨-, hBξ, -⟩ := not_mem_bad.mp hξ
    obtain ⟨η, hη⟩ := exists_nonsingular W ξ
    exact (hφ ξ η hη hBξ).1
  have hb' : ∀ ξ ∉ bad Bα B N₁, aeval ξ (q * N₁) ≠ 0 := fun ξ hξ => by
    obtain ⟨hBαξ, -, hNξ⟩ := not_mem_bad.mp hξ
    obtain ⟨η, hη⟩ := exists_nonsingular W ξ
    rw [map_mul]
    exact mul_ne_zero (hc ξ η hη hBαξ).1 hNξ
  have hconst : ∀ ξ₁ ∉ bad Bα B N₁, ∀ ξ₂ ∉ bad Bα B N₁,
      aeval ξ₁ P / aeval ξ₁ S ∉ {x' : k | aeval x' W₂.Ψ₂Sq = 0} →
      aeval ξ₁ P / aeval ξ₁ S = aeval ξ₂ P / aeval ξ₂ S →
        (aeval ξ₁ (p₀ * N₁ - p₁ * N₀) / aeval ξ₁ (q * N₁) =
            aeval ξ₂ (p₀ * N₁ - p₁ * N₀) / aeval ξ₂ (q * N₁) ∧
          aeval ξ₁ (p₁ * R) / aeval ξ₁ (q * N₁) =
            aeval ξ₂ (p₁ * R) / aeval ξ₂ (q * N₁)) := by
    intro ξ₁ hξ₁ ξ₂ hξ₂ hTx hθ
    obtain ⟨hBα₁, hB₁, hN₁⟩ := not_mem_bad.mp hξ₁
    obtain ⟨hBα₂, hB₂, hN₂⟩ := not_mem_bad.mp hξ₂
    refine fibre_const hker hc hφ hBα₁ hB₁ hN₁ hBα₂ hB₂ hN₂
      (div_mul_cancel₀ _ (hS' ξ₁ hξ₁)) ?_ hTx
    rw [hθ]
    exact div_mul_cancel₀ _ (hS' ξ₂ hξ₂)
  obtain ⟨c, e, T₁, hT₁, H₁⟩ := Polynomial.SepFibreDescent.descent hPm hdeg hcop hG hT hS' hb'
    (fun ξ₁ h₁ ξ₂ h₂ hx hθ => (hconst ξ₁ h₁ ξ₂ h₂ hx hθ).1)
  obtain ⟨c', e', T₂, hT₂, H₂⟩ := Polynomial.SepFibreDescent.descent hPm hdeg hcop hG hT hS' hb'
    (fun ξ₁ h₁ ξ₂ h₂ hx hθ => (hconst ξ₁ h₁ ξ₂ h₂ hx hθ).2)
  refine ⟨c, e, c', e', T₁ ∪ T₂, hT₁.union hT₂, fun x' hx' => ?_⟩
  simp only [Set.mem_union, not_or] at hx'
  obtain ⟨he, H₁'⟩ := H₁ x' hx'.1
  obtain ⟨he', H₂'⟩ := H₂ x' hx'.2
  refine ⟨he, he', fun ξ hξ η h y' h' hn => ?_⟩
  obtain ⟨hBαξ, hBξ, hNξ⟩ := not_mem_bad.mp hξ
  obtain ⟨hSξ, -, hx, -⟩ := phi_coords hφ hBξ hn
  have hθ : aeval ξ P / aeval ξ S = x' := by
    rw [div_eq_iff hSξ, ← hx]
  rw [(coord_formula hc hφ hBαξ hBξ hNξ hn).2, H₁' ξ hξ hθ, H₂' ξ hξ hθ]

def xc : (W₃.baseChange k).toAffine.Point → k
  | .zero => 0
  | .some x _ _ => x

def yc : (W₃.baseChange k).toAffine.Point → k
  | .zero => 0
  | .some _ y _ => y

omit [IsAlgClosed k] [DecidableEq k] [W.IsElliptic] [W₂.IsElliptic] in
theorem some_eq_some {x y x' y' : k} (h : (W₃.baseChange k).toAffine.Nonsingular x y)
    (hx : x = x') (hy : y = y') :
    ∃ h', Affine.Point.some x y h = Affine.Point.some x' y' h' := by
  subst hx hy
  exact ⟨h, rfl⟩

theorem represented (hPm : P.Monic) (hdeg : P.natDegree = S.natDegree + 1)
    (hcop : IsCoprime P S) (hker : ∀ T, φ T = 0 → α T = 0)
    {β : (W₂.baseChange k).toAffine.Point →+ (W₃.baseChange k).toAffine.Point}
    (hβ : ∀ T, β (φ T) = α T) {nX dX nY dY : F[X][Y]} (hBα : Bα.Finite)
    (hrep : ∀ (x y : k) (h : (W.baseChange k).toAffine.Nonsingular x y), x ∉ Bα →
      evalEvalBC k dX x y ≠ 0 ∧ evalEvalBC k dY x y ≠ 0 ∧
        ∃ h', α (.some x y h) = .some (evalEvalBC k nX x y / evalEvalBC k dX x y)
          (evalEvalBC k nY x y / evalEvalBC k dY x y) h')
    (hB : B.Finite) (hφ : SepShape φ P S N₀ N₁ R B) :
    IsRationallyRepresented k W₂ W₃ β := by
  have hN1 : N₁ ≠ 0 := N₁_ne_zero hPm hdeg hB hφ

  obtain ⟨p₀, p₁, q, hpq⟩ := exists_ratio_linear (k := k) W nX dX
  have hcx : CoordSpec α xc Bα p₀ p₁ q := by
    intro ξ η h hξ
    obtain ⟨hdX, -, h', hαQ⟩ := hrep ξ η h hξ
    obtain ⟨hdX', -, -, -⟩ := hrep ξ _ ((WeierstrassCurve.Affine.nonsingular_neg ..).mpr h) hξ
    rw [evalEvalBC_eq_bc] at hdX hdX'
    obtain ⟨hq, e⟩ := hpq ξ η h.left hdX hdX'
    refine ⟨hq, ?_⟩
    rw [hαQ, xc, evalEvalBC_eq_bc, evalEvalBC_eq_bc, e]
  obtain ⟨r₀, r₁, s, hrs⟩ := exists_ratio_linear (k := k) W nY dY
  have hcy : CoordSpec α yc Bα r₀ r₁ s := by
    intro ξ η h hξ
    obtain ⟨-, hdY, h', hαQ⟩ := hrep ξ η h hξ
    obtain ⟨-, hdY', -, -⟩ := hrep ξ _ ((WeierstrassCurve.Affine.nonsingular_neg ..).mpr h) hξ
    rw [evalEvalBC_eq_bc] at hdY hdY'
    obtain ⟨hs, e⟩ := hrs ξ η h.left hdY hdY'
    refine ⟨hs, ?_⟩
    rw [hαQ, yc, evalEvalBC_eq_bc, evalEvalBC_eq_bc, e]
  obtain ⟨c₁, e₁, c₂, e₂, Tx, hTx, Hx⟩ := descent_pair hPm hdeg hcop hker hcx hφ hN1 hBα hB
  obtain ⟨c₃, e₃, c₄, e₄, Ty, hTy, Hy⟩ := descent_pair hPm hdeg hcop hker hcy hφ hN1 hBα hB
  have hG : (bad (k := k) Bα B N₁).Finite := finite_bad hBα hB hN1
  refine ⟨C (c₁ * e₂) + C (c₂ * e₁) * Y, C (e₁ * e₂), C (c₃ * e₄) + C (c₄ * e₃) * Y, C (e₃ * e₄),
    Tx ∪ Ty ∪ (fun ξ => aeval ξ P / aeval ξ S) '' bad Bα B N₁,
    (hTx.union hTy).union (hG.image _), fun x' y' h hx' => ?_⟩
  simp only [Set.mem_union, not_or, Set.mem_image, not_exists, not_and] at hx'
  obtain ⟨⟨hxTx, hxTy⟩, hxG⟩ := hx'
  obtain ⟨hex₁, hex₂, Hx'⟩ := Hx x' hxTx
  obtain ⟨hey₁, hey₂, Hy'⟩ := Hy x' hxTy
  simp only [evalEvalBC_eq_bc, map_add, map_mul, bc_C, bc_X]
  refine ⟨mul_ne_zero hex₁ hex₂, mul_ne_zero hey₁ hey₂, ?_⟩

  obtain ⟨ξ, hSξ, hθ⟩ := exists_mem_fibre (k := k) hPm hdeg hcop x'
  have hξG : ξ ∉ bad Bα B N₁ := fun hmem => hxG ξ hmem hθ
  obtain ⟨hBαξ, hBξ, -⟩ := not_mem_bad.mp hξG
  obtain ⟨η, hη, hn⟩ := exists_lift hφ hBξ h (by rw [← hθ, div_mul_cancel₀ _ hSξ])
  have hβ' : β (.some x' y' h) = α (.some ξ η hη) := by rw [← hn, hβ]
  obtain ⟨-, -, h'', hαQ⟩ := hrep ξ η hη hBαξ
  have HX := Hx' ξ hξG η hη y' h hn
  have HY := Hy' ξ hξG η hη y' h hn
  rw [hαQ] at HX HY
  rw [hβ', hαQ]
  refine some_eq_some h'' ?_ ?_
  · rw [show evalEvalBC k nX ξ η / evalEvalBC k dX ξ η = _ from HX]
    field_simp
  · rw [show evalEvalBC k nY ξ η / evalEvalBC k dY ξ η = _ from HY]
    field_simp

end Assembly

theorem main [IsAlgClosed k] [DecidableEq k] (W₁ W₂ W₃ : WeierstrassCurve F) [W₁.IsElliptic]
    [W₂.IsElliptic] [W₃.IsElliptic]
    {φ : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point}
    {α : (W₁.baseChange k).toAffine.Point →+ (W₃.baseChange k).toAffine.Point}
    (hα : α ∈ rationalHomSet k W₁ W₃) {P S N₀ N₁ R : F[X]} (hP : P.Monic)
    (hdeg : P.natDegree = S.natDegree + 1) (hcop : IsCoprime P S) {B : Set k} (hB : B.Finite)
    (hφ : SepShape φ P S N₀ N₁ R B) (hker : ∀ T, φ T = 0 → α T = 0) :
    ∃ β ∈ rationalHomSet k W₂ W₃, ∀ T, α T = β (φ T) := by
  have hφmem : φ ∈ rationalHomSet k W₁ W₂ := mem_rationalHomSet_of_sepShape hB hφ
  have hφ0 : φ ≠ 0 := ne_zero_of_sepShape hB hφ
  have hsurj := WeierstrassCurve.surjective_of_mem_rationalHomSet k hφmem hφ0
  obtain ⟨β, hβ⟩ := exists_hom_of_ker φ hsurj α hker
  refine ⟨β, ?_, fun T => (hβ T).symm⟩
  rcases hα with hα0 | ⟨nX, dX, nY, dY, Bα, hBα, hrep⟩
  · subst hα0
    left
    ext T
    obtain ⟨Q, rfl⟩ := hsurj T
    rw [hβ]
    rfl
  · right
    exact represented hP hdeg hcop hker hβ hBα hrep hB hφ

end WeierstrassCurve.SepIsogFactor
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_comp_eq_of_ker_le_of_separable.WeierstrassCurve P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_comp_eq_of_ker_le_of_separable.WeierstrassCurve.SepIsogFactor"
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_comp_eq_of_ker_le_of_separable.WeierstrassCurve"

theorem solution
    {F : Type*} [Field F] (k : Type*) [Field k] [DecidableEq k] [Algebra F k] [IsAlgClosed k]
    (W₁ W₂ W₃ : WeierstrassCurve F) [W₁.IsElliptic] [W₂.IsElliptic] [W₃.IsElliptic]
    {φ : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point}
    {α : (W₁.baseChange k).toAffine.Point →+ (W₃.baseChange k).toAffine.Point}
    (hα : α ∈ WeierstrassCurve.rationalHomSet k W₁ W₃)
    {P S N₀ N₁ R : F[X]} (hP : P.Monic) (hdeg : P.natDegree = S.natDegree + 1)
    (hcop : IsCoprime P S) {B : Set k} (hB : B.Finite)
    (hφ : ∀ (x y : k) (h : (W₁.baseChange k).toAffine.Nonsingular x y), x ∉ B →
      aeval x S ≠ 0 ∧ aeval x R ≠ 0 ∧
      ∃ h', φ (.some x y h) =
        .some (aeval x P / aeval x S) ((aeval x N₀ + aeval x N₁ * y) / aeval x R) h')
    (hker : ∀ T, φ T = 0 → α T = 0) :
    ∃ β ∈ WeierstrassCurve.rationalHomSet k W₂ W₃, ∀ T, α T = β (φ T) :=
  WeierstrassCurve.SepIsogFactor.main W₁ W₂ W₃ hα hP hdeg hcop hB hφ hker

end S_WeierstrassCurve_exists_mem_rationalHomSet_comp_eq_of_ker_le_of_separable
end P2MW
export P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_comp_eq_of_ker_le_of_separable (solution)
