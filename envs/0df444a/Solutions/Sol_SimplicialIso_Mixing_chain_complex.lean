-- Prove2me | solution 1 for SimplicialIso.Mixing.chain_complex
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T04:17:05.160279+00:00
-- url     : https://prove2.me/submissions/ea97860a-4cd9-4fae-8df9-abd22a18a9b4

import Definitions.Def_SimplicialIso_Mixing_Setting
import Mathlib.Analysis.InnerProductSpace.ExteriorPower
open Finset Matrix
open scoped BigOperators InnerProductSpace Classical
open SimplicialIso.Mixing


open Finset Matrix
open scoped BigOperators InnerProductSpace Classical
open SimplicialIso.Mixing

namespace SimplicialMixingProof

noncomputable def constantOne (n : ℕ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun _ => 1)

@[simp] theorem constantOne_apply (n : ℕ) (i : Fin n) : constantOne n i = 1 := rfl

noncomputable def wedgeForm {n k : ℕ} (v : Fin k → EuclideanSpace ℝ (Fin n)) :
    Form n k :=
  ((EuclideanSpace.basisFun (Fin n) ℝ).exteriorPower k).repr
    (exteriorPower.ιMulti ℝ k v)

theorem wedge_inner {n k : ℕ} (v w : Fin k → EuclideanSpace ℝ (Fin n)) :
    ⟪wedgeForm v, wedgeForm w⟫_ℝ =
      (Matrix.of fun i j => ⟪v j, w i⟫_ℝ).det := by
  have h := (((EuclideanSpace.basisFun (Fin n) ℝ).exteriorPower k).repr.inner_map_map
    (exteriorPower.ιMulti ℝ k v) (exteriorPower.ιMulti ℝ k w)).trans
      (exteriorPower.inner_ιMulti_ιMulti v w)
  let e : Cell n k ≃ Set.powersetCard (Fin n) k := Equiv.refl _
  change (∑ i : Cell n k, ⟪wedgeForm v i, wedgeForm w i⟫_ℝ) = _
  calc
    _ = ∑ i : Set.powersetCard (Fin n) k,
        ⟪wedgeForm v i, wedgeForm w i⟫_ℝ :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = _ := by
      change ⟪((EuclideanSpace.basisFun (Fin n) ℝ).exteriorPower k).repr
          (exteriorPower.ιMulti ℝ k v),
        ((EuclideanSpace.basisFun (Fin n) ℝ).exteriorPower k).repr
          (exteriorPower.ιMulti ℝ k w)⟫_ℝ = _
      exact h

theorem wedge_apply {n k : ℕ} (v : Fin k → EuclideanSpace ℝ (Fin n))
    (σ : Cell n k) :
    wedgeForm v σ = (Matrix.of fun i j => v i (σ.val.orderEmbOfFin σ.property j)).det := by
  change (((EuclideanSpace.basisFun (Fin n) ℝ).exteriorPower k).repr
    (exteriorPower.ιMulti ℝ k v)) (show Set.powersetCard (Fin n) k from σ) = _
  rw [← OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.toBasis_exteriorPower, exteriorPower.basis_repr_apply,
    exteriorPower.ιMultiDual_apply_ιMulti]
  simp only [Module.Basis.coord_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr]
  rfl

theorem wedge_span (n k : ℕ) :
    Submodule.span ℝ (Set.range (wedgeForm (n := n) (k := k))) = ⊤ := by
  let e := ((EuclideanSpace.basisFun (Fin n) ℝ).exteriorPower k).repr
  have h := congrArg (Submodule.map e.toLinearEquiv.toLinearMap)
    (exteriorPower.ιMulti_span ℝ k (EuclideanSpace ℝ (Fin n)))
  change Submodule.span ℝ (Set.range (fun v => e (exteriorPower.ιMulti ℝ k v))) = ⊤
  simpa [Submodule.map_span, ← Set.range_comp, Function.comp_def] using h

end SimplicialMixingProof

open Finset Matrix
open scoped BigOperators InnerProductSpace Classical
open SimplicialIso.Mixing

namespace SimplicialMixingProof

theorem erase_card {n k : ℕ} (σ : Cell n (k + 1)) (j : Fin (k + 1)) :
    (σ.val.erase (σ.val.orderEmbOfFin σ.property j)).card = k := by
  rw [Finset.card_erase_of_mem (Finset.orderEmbOfFin_mem _ _ _), σ.property]
  omega

theorem order_erase {n k : ℕ} (σ : Cell n (k + 1)) (j : Fin (k + 1)) (i : Fin k) :
    (σ.val.erase (σ.val.orderEmbOfFin σ.property j)).orderEmbOfFin (erase_card σ j) i =
      σ.val.orderEmbOfFin σ.property (j.succAbove i) := by
  have h := Finset.orderEmbOfFin_unique (erase_card σ j)
    (f := fun i : Fin k => σ.val.orderEmbOfFin σ.property (j.succAbove i))
    (fun i => Finset.mem_erase.mpr ⟨by
      intro he
      exact j.succAbove_ne i ((σ.val.orderEmbOfFin σ.property).injective he),
      Finset.orderEmbOfFin_mem _ _ _⟩)
    ((σ.val.orderEmbOfFin σ.property).strictMono.comp j.succAboveOrderEmb.strictMono)
  exact congrFun h.symm i

theorem smaller_card {n k : ℕ} (σ : Cell n k) (j : Fin k) :
    (σ.val.filter (· < σ.val.orderEmbOfFin σ.property j)).card = j.val := by
  let e := σ.val.orderEmbOfFin σ.property
  have hs : σ.val.filter (· < e j) = (Finset.Iio j).image e := by
    ext v
    constructor
    · intro hv
      obtain ⟨hv, hj⟩ := Finset.mem_filter.mp hv
      have hr : v ∈ Set.range e := by
        rw [Finset.range_orderEmbOfFin]
        exact hv
      obtain ⟨i, rfl⟩ := hr
      exact Finset.mem_image.mpr ⟨i, Finset.mem_Iio.mpr (e.lt_iff_lt.mp hj), rfl⟩
    · intro hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_filter.mpr ⟨Finset.orderEmbOfFin_mem _ _ _,
        e.strictMono (Finset.mem_Iio.mp hi)⟩
  rw [hs, Finset.card_image_of_injective _ e.injective]
  simp

theorem sgn_order {n k : ℕ} (σ : Cell n k) (j : Fin k) :
    sgn σ.val (σ.val.orderEmbOfFin σ.property j) = (-1 : ℝ) ^ j.val := by
  rw [sgn, smaller_card]

end SimplicialMixingProof

open Finset Matrix
open scoped BigOperators InnerProductSpace Classical
open SimplicialIso.Mixing

namespace SimplicialMixingProof

theorem sum_order {n k : ℕ} (σ : Cell n k) (f : Fin n → ℝ) :
    (∑ j : Fin k, f (σ.val.orderEmbOfFin σ.property j)) = ∑ v ∈ σ.val, f v := by
  rw [← Finset.sum_image (fun i _ j _ h => (σ.val.orderEmbOfFin σ.property).injective h)]
  rw [Finset.image_orderEmbOfFin_univ]

theorem cobdLow_wedge {n k : ℕ} (v : Fin k → EuclideanSpace ℝ (Fin n)) :
    cobdLow n (k + 1) (wedgeForm v) = wedgeForm (Fin.cons (constantOne n) v) := by
  ext τ
  change (∑ a ∈ τ.val, sgn τ.val a * ev (wedgeForm v) (τ.val.erase a)) = _
  rw [← sum_order τ, wedge_apply, Matrix.det_succ_row_zero]
  apply Finset.sum_congr rfl
  intro j _
  rw [sgn_order, ev, dif_pos (erase_card τ j), wedge_apply]
  simp only [Matrix.of_apply, Fin.cons_zero, constantOne_apply, mul_one]
  congr 2
  ext i l
  simp only [Matrix.submatrix_apply, Matrix.of_apply, Fin.cons_succ, order_erase]

theorem cobdTop_wedge {n k : ℕ} (X : Complex n k)
    (v : Fin k → EuclideanSpace ℝ (Fin n)) (τ : Cell n (k + 1)) :
    cobdTop X (wedgeForm v) τ =
      if τ.val ∈ X.top then wedgeForm (Fin.cons (constantOne n) v) τ else 0 := by
  have h := congrArg (fun f : Form n (k + 1) => f τ) (cobdLow_wedge v)
  change (∑ a ∈ τ.val, sgn τ.val a * ev (wedgeForm v) (τ.val.erase a)) = _ at h
  change (if τ.val ∈ X.top then
    ∑ a ∈ τ.val, sgn τ.val a * ev (wedgeForm v) (τ.val.erase a) else 0) = _
  rw [h]

theorem cobdTop_cobdLow {n k : ℕ} (X : Complex n (k + 1))
    (f : Form n k) : cobdTop X (cobdLow n (k + 1) f) = 0 := by
  have hh : cobdTop X ∘ₗ cobdLow n (k + 1) = 0 := by
    apply LinearMap.ext_on (wedge_span n k)
    rintro _ ⟨v, rfl⟩
    ext τ
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, PiLp.zero_apply]
    rw [cobdLow_wedge, cobdTop_wedge]
    split_ifs
    · rw [wedge_apply]
      apply Matrix.det_zero_of_row_eq (i := (0 : Fin (k + 2))) (j := 1) (by intro h; have hh := congrArg Fin.val h; simp at hh)
      ext j
      simp
    · rfl
  exact LinearMap.congr_fun hh f

end SimplicialMixingProof

open Finset Matrix
open scoped BigOperators InnerProductSpace Classical
open SimplicialIso.Mixing

namespace SimplicialMixingProof

def insertCell {n k : ℕ} (σ : Cell n k) (v : {v : Fin n // v ∉ σ.val}) :
    Cell n (k + 1) :=
  ⟨insert v.val σ.val, by rw [Finset.card_insert_of_notMem v.property, σ.property]⟩

def eraseCell {n k : ℕ} (τ : Cell n (k + 1)) (v : {v : Fin n // v ∈ τ.val}) :
    Cell n k :=
  ⟨τ.val.erase v.val, by rw [Finset.card_erase_of_mem v.property, τ.property]; omega⟩

noncomputable def incidenceEquiv (n k : ℕ) :
    (Σ σ : Cell n k, {v : Fin n // v ∉ σ.val}) ≃
      (Σ τ : Cell n (k + 1), {v : Fin n // v ∈ τ.val}) where
  toFun p := ⟨insertCell p.1 p.2, ⟨p.2.val, Finset.mem_insert_self _ _⟩⟩
  invFun p := ⟨eraseCell p.1 p.2, ⟨p.2.val, Finset.notMem_erase _ _⟩⟩
  left_inv p := by
    rcases p with ⟨σ, v, hv⟩
    apply Sigma.ext (Subtype.ext (Finset.erase_insert hv))
    apply (Subtype.heq_iff_coe_eq (fun x => by
      change (x ∉ (insert v σ.val).erase v) ↔ x ∉ σ.val
      rw [Finset.erase_insert hv])).mpr
    rfl
  right_inv p := by
    rcases p with ⟨τ, v, hv⟩
    apply Sigma.ext (Subtype.ext (Finset.insert_erase hv))
    apply (Subtype.heq_iff_coe_eq (fun x => by
      change (x ∈ insert v (τ.val.erase v)) ↔ x ∈ τ.val
      rw [Finset.insert_erase hv])).mpr
    rfl

theorem sum_incidence {n k : ℕ}
    (f : (τ : Cell n (k + 1)) → {v : Fin n // v ∈ τ.val} → ℝ) :
    (∑ σ : Cell n k, ∑ v : {v : Fin n // v ∉ σ.val},
      f (insertCell σ v) ⟨v.val, Finset.mem_insert_self _ _⟩) =
    ∑ τ : Cell n (k + 1), ∑ v : {v : Fin n // v ∈ τ.val}, f τ v := by
  simpa only [Fintype.sum_sigma] using
    (Fintype.sum_equiv (incidenceEquiv n k)
      (fun p => f (insertCell p.1 p.2) ⟨p.2.val, Finset.mem_insert_self _ _⟩)
      (fun p => f p.1 p.2) (fun _ => rfl))

end SimplicialMixingProof

open Finset Matrix
open scoped BigOperators InnerProductSpace Classical
open SimplicialIso.Mixing

namespace SimplicialMixingProof

theorem bdTop_apply_subtype {n k : ℕ} (X : Complex n k) (g : Form n (k + 1))
    (σ : Cell n k) :
    bdTop X g σ = ∑ v : {v : Fin n // v ∉ σ.val},
      if (insertCell σ v).val ∈ X.top then
        sgn (insertCell σ v).val v.val * g (insertCell σ v) else 0 := by
  change (∑ v ∈ Finset.univ.filter (fun v => v ∉ σ.val ∧ insert v σ.val ∈ X.top),
    sgn (insert v σ.val) v * ev g (insert v σ.val)) = _
  calc
    _ = ∑ v ∈ Finset.univ.filter (fun v => v ∉ σ.val),
        if insert v σ.val ∈ X.top then sgn (insert v σ.val) v * ev g (insert v σ.val)
        else 0 := by
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro v _
      by_cases h : v ∉ σ.val <;> simp [h]
    _ = ∑ v : {v : Fin n // v ∉ σ.val},
        if insert v.val σ.val ∈ X.top then
          sgn (insert v.val σ.val) v.val * ev g (insert v.val σ.val) else 0 :=
      Finset.sum_subtype _ (by simp) _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v _
      simp only [ev, insertCell, Finset.card_insert_of_notMem v.property, σ.property, dif_pos]
      rfl

theorem cobdTop_apply_subtype {n k : ℕ} (X : Complex n k) (f : Form n k)
    (τ : Cell n (k + 1)) :
    cobdTop X f τ = if τ.val ∈ X.top then
      ∑ v : {v : Fin n // v ∈ τ.val}, sgn τ.val v.val * f (eraseCell τ v) else 0 := by
  change (if τ.val ∈ X.top then ∑ v ∈ τ.val, sgn τ.val v * ev f (τ.val.erase v) else 0) = _
  congr 1
  rw [Finset.sum_subtype (p := fun v => v ∈ τ.val) τ.val (fun _ => Iff.rfl)]
  apply Finset.sum_congr rfl
  intro v _
  simp only [ev, eraseCell, Finset.card_erase_of_mem v.property, τ.property, Nat.add_sub_cancel, dif_pos]

theorem inner_bdTop {n k : ℕ} (X : Complex n k) (g : Form n (k + 1))
    (f : Form n k) : ⟪bdTop X g, f⟫_ℝ = ⟪g, cobdTop X f⟫_ℝ := by
  have h := sum_incidence (fun τ v =>
    if τ.val ∈ X.top then sgn τ.val v.val * g τ * f (eraseCell τ v) else 0)
  simp only [eraseCell, insertCell] at h
  change (∑ σ : Cell n k, f σ * bdTop X g σ) =
    ∑ τ : Cell n (k + 1), cobdTop X f τ * g τ
  simp only [bdTop_apply_subtype, cobdTop_apply_subtype,
    Finset.mul_sum, Finset.sum_mul, mul_ite, ite_mul, mul_zero, zero_mul]
  convert h using 1
  · apply Finset.sum_congr rfl
    intro σ _
    apply Finset.sum_congr rfl
    intro v _
    have he : (⟨(insert v.val σ.val).erase v.val, by
        rw [Finset.erase_insert v.property]; exact σ.property⟩ : Cell n k) = σ :=
      Subtype.ext (Finset.erase_insert v.property)
    rw [he]
    dsimp only [insertCell]
    split_ifs <;> ring
  · apply Finset.sum_congr rfl
    intro τ _
    by_cases ht : τ.val ∈ X.top
    · simp only [ht, if_true]
      apply Finset.sum_congr rfl
      intro v _
      simp only [eraseCell]
      ring
    · simp [ht]

end SimplicialMixingProof

open Finset Matrix
open scoped BigOperators InnerProductSpace Classical
open SimplicialIso.Mixing

namespace SimplicialMixingProof

def completeComplex (n k : ℕ) : Complex n k where
  top := Finset.univ.powersetCard (k + 1)
  card_top _ h := (Finset.mem_powersetCard.mp h).2

theorem bdLow_eq_complete {n k : ℕ} (g : Form n (k + 1)) :
    bdLow n (k + 1) g = bdTop (completeComplex n k) g := by
  ext σ
  simp only [bdLow, bdTop, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp,
    completeComplex, Finset.mem_powersetCard, Finset.subset_univ, true_and]
  apply Finset.sum_congr
  · ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hv
      exact ⟨hv, by rw [Finset.card_insert_of_notMem hv, σ.property]; omega⟩
    · exact And.left
  · intro v _
    rfl

theorem cobdLow_eq_complete {n k : ℕ} (f : Form n k) :
    cobdLow n (k + 1) f = cobdTop (completeComplex n k) f := by
  ext τ
  simp [cobdLow, cobdTop, completeComplex, τ.property]

theorem inner_bdLow {n k : ℕ} (g : Form n (k + 1)) (f : Form n k) :
    ⟪bdLow n (k + 1) g, f⟫_ℝ = ⟪g, cobdLow n (k + 1) f⟫_ℝ := by
  rw [bdLow_eq_complete, cobdLow_eq_complete, inner_bdTop]


end SimplicialMixingProof

/- Boundary and exterior-power lemmas above are adapted from sometik179's
   accepted submission ffdcaf50-1fb5-4373-992c-4a96d8738b90. -/
theorem solution (n d : ℕ) (hd : 1 ≤ d) (X : Complex n d) :
    (∀ g : Form n (d + 1), bdLow n d (bdTop X g) = 0) ∧
      (∀ h : Form n (d - 1), cobdTop X (cobdLow n d h) = 0) := by
  cases d with
  | zero => omega
  | succ k =>
    refine ⟨?_, fun h => SimplicialMixingProof.cobdTop_cobdLow X h⟩
    intro g
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [SimplicialMixingProof.inner_bdLow, SimplicialMixingProof.inner_bdTop,
      SimplicialMixingProof.cobdTop_cobdLow, inner_zero_right]

#print axioms solution
