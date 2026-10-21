-- Prove2me | solution 1 for SimplicialIso.Mixing.theorem_1_4
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-21T02:38:59.810859+00:00
-- url     : https://prove2.me/submissions/ffdcaf50-1fb5-4373-992c-4a96d8738b90

import Mathlib
import Definitions.Def_SimplicialIso_Mixing_Setting
open Finset Matrix
open scoped BigOperators InnerProductSpace Classical
open SimplicialIso.Mixing

namespace SimplicialMixingProof

end SimplicialMixingProof

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

theorem wedge_mem_cycles {n d : ℕ} (hd : 1 ≤ d)
    (v : Fin d → EuclideanSpace ℝ (Fin n)) (hsum : ∀ i, ∑ j, v i j = 0) :
    wedgeForm v ∈ cycles n d := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  have h : (innerₗ (Form n (k + 1)) (wedgeForm v)).comp (cobdLow n (k + 1)) = 0 := by
    apply LinearMap.ext_on (wedge_span n k)
    rintro _ ⟨w, rfl⟩
    change ⟪wedgeForm v, cobdLow n (k + 1) (wedgeForm w)⟫_ℝ = 0
    rw [cobdLow_wedge, wedge_inner]
    apply Matrix.det_eq_zero_of_row_eq_zero 0
    intro j
    simpa [constantOne, PiLp.inner_apply, RCLike.inner_apply] using hsum j
  change bdLow n (k + 1) (wedgeForm v) = 0
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  rw [inner_bdLow]
  exact LinearMap.congr_fun h _

theorem upLap_isSymmetric {n d : ℕ} (X : Complex n d) : (upLap X).IsSymmetric := by
  intro f g
  change ⟪bdTop X (cobdTop X f), g⟫_ℝ = ⟪f, bdTop X (cobdTop X g)⟫_ℝ
  calc
    _ = ⟪cobdTop X f, cobdTop X g⟫_ℝ := inner_bdTop X _ _
    _ = ⟪cobdTop X g, cobdTop X f⟫_ℝ := real_inner_comm _ _
    _ = ⟪bdTop X (cobdTop X g), f⟫_ℝ := (inner_bdTop X _ _).symm
    _ = _ := real_inner_comm _ _

theorem upLap_mem_cycles {n d : ℕ} (hd : 1 ≤ d) (X : Complex n d) (f : Form n d) :
    upLap X f ∈ cycles n d := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  change bdLow n (k + 1) (upLap X f) = 0
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  rw [inner_bdLow]
  change ⟪bdTop X (cobdTop X f), _⟫_ℝ = 0
  rw [inner_bdTop, cobdTop_cobdLow, inner_zero_right]

end SimplicialMixingProof

open Finset Matrix
open scoped BigOperators Classical

namespace SimplicialMixingProof

noncomputable section

def borderDiag {k : ℕ} (a : ℝ) (r c : Fin k → ℝ) : Matrix (Fin (k+1)) (Fin (k+1)) ℝ :=
  Fin.cons (Fin.cons a r) (fun i => Fin.cons 0 (fun j => if i = j then c i else 0))

theorem det_borderDiag {k : ℕ} (a : ℝ) (r c : Fin k → ℝ) :
    (borderDiag a r c).det = a * ∏ i, c i := by
  have hm : (borderDiag a r c).submatrix Fin.succ Fin.succ = Matrix.diagonal c := by
    ext i j
    rfl
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have hz (i : Fin k) : borderDiag a r c i.succ 0 = 0 := rfl
  simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero,
    pow_zero, one_mul, Fin.succAbove_zero]
  change a * ((borderDiag a r c).submatrix Fin.succ Fin.succ).det = _
  rw [hm, Matrix.det_diagonal]

def centeredGram {k : ℕ} (n a b : ℝ) (c : Fin k → ℝ) :
    Matrix (Fin (k+1)) (Fin (k+1)) ℝ :=
  Fin.cons (fun j => -(b / n) * (Fin.cons a c : Fin (k+1) → ℝ) j)
    (fun i j => (if j = i.succ then c i else 0) - (c i / n) * (Fin.cons a c : Fin (k+1) → ℝ) j)

theorem det_centeredGram {k : ℕ} (n a b : ℝ) (c : Fin k → ℝ) (hb : b ≠ 0) :
    (centeredGram n a b c).det = -(b / n) * a * ∏ i, c i := by
  let B := borderDiag (-(b / n) * a) (fun i => -(b / n) * c i) c
  have he : (centeredGram n a b c).det = B.det := by
    apply Matrix.det_eq_of_forall_row_eq_smul_add_const
      (Fin.cons 0 (fun i => c i / b)) 0 (by simp)
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j <;> simp [centeredGram, B, borderDiag]
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp only [centeredGram, B, borderDiag, Fin.cons_succ, Fin.cons_zero,
          Ne.symm (Fin.succ_ne_zero i), if_false, zero_sub, zero_add]
        field_simp [hb]
      · simp only [centeredGram, B, borderDiag, Fin.cons_succ, Fin.cons_zero,
          Fin.succ_inj]
        by_cases hij : i = j
        · subst j
          simp only [ite_true]
          field_simp [hb]
          ring
        · simp only [if_neg hij, if_neg (Ne.symm hij), zero_sub, zero_add]
          field_simp [hb]
  rw [he, det_borderDiag]

def topCrossGram {k : ℕ} (r a b : ℝ) (c : Fin k → ℝ) :
    Matrix (Fin (k+2)) (Fin (k+2)) ℝ :=
  Fin.cons (Fin.cons r (Fin.cons a c))
    (Fin.cons (Fin.cons b (fun _ => 0))
      (fun i => Fin.cons (c i) (Fin.cons 0 (fun j => if i = j then c i else 0))))

theorem det_topCrossGram {k : ℕ} (r a b : ℝ) (c : Fin k → ℝ) :
    (topCrossGram r a b c).det = -(a * b * ∏ i, c i) := by
  rw [Matrix.det_succ_row _ (0 : Fin (k+1)).succ, Fin.sum_univ_succ]
  simp only [topCrossGram, Fin.cons_succ, Fin.cons_zero, Fin.val_succ, Fin.val_zero,
    zero_add, pow_one, mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
    Fin.succAbove_zero]
  have hm : (topCrossGram r a b c).submatrix (0 : Fin (k+1)).succ.succAbove Fin.succ =
      borderDiag a c c := by
    ext i j
    change topCrossGram r a b c ((0 : Fin (k+1)).succ.succAbove i) j.succ =
      borderDiag a c c i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j <;> simp [topCrossGram, borderDiag]
    · refine Fin.cases ?_ (fun j => ?_) j <;> simp [topCrossGram, borderDiag]
  change -1 * b * ((topCrossGram r a b c).submatrix
    (0 : Fin (k+1)).succ.succAbove Fin.succ).det = _
  rw [hm, det_borderDiag]
  ring

end
end SimplicialMixingProof

open Finset Matrix
open scoped BigOperators InnerProductSpace Classical
open SimplicialIso.Mixing

namespace SimplicialMixingProof

noncomputable def indicatorVec {n : ℕ} (A : Finset (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun v => if v ∈ A then 1 else 0)

@[simp] theorem indicatorVec_apply {n : ℕ} (A : Finset (Fin n)) (v : Fin n) :
    indicatorVec A v = if v ∈ A then 1 else 0 := rfl

theorem indicator_inner {n : ℕ} (A B : Finset (Fin n)) :
    ⟪indicatorVec A, indicatorVec B⟫_ℝ = ((A ∩ B).card : ℝ) := by
  rw [PiLp.inner_apply]
  have he (v : Fin n) : ⟪indicatorVec A v, indicatorVec B v⟫_ℝ =
      if v ∈ A ∩ B then (1 : ℝ) else 0 := by
    by_cases ha : v ∈ A <;> by_cases hb : v ∈ B <;> simp [ha, hb]
  simp_rw [he]
  simp only [Finset.sum_boole, Finset.mem_inter]
  congr 2
  ext x
  simp

theorem indicator_one {n : ℕ} (A : Finset (Fin n)) :
    ⟪indicatorVec A, constantOne n⟫_ℝ = (A.card : ℝ) := by
  rw [PiLp.inner_apply]
  simp [indicatorVec, constantOne, RCLike.inner_apply]

@[simp] theorem one_inner_one (n : ℕ) :
    ⟪constantOne n, constantOne n⟫_ℝ = (n : ℝ) := by
  rw [PiLp.inner_apply]
  simp [constantOne]

noncomputable def centeredVec {n : ℕ} (A : Finset (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  indicatorVec A - ((A.card : ℝ) / n) • constantOne n

theorem centered_one {n : ℕ} (hn : n ≠ 0) (A : Finset (Fin n)) :
    ⟪centeredVec A, constantOne n⟫_ℝ = 0 := by
  rw [centeredVec, inner_sub_left, inner_smul_left, indicator_one, one_inner_one]
  simp [hn]

theorem indicator_centered {n : ℕ} (A B : Finset (Fin n)) :
    ⟪indicatorVec A, centeredVec B⟫_ℝ =
      ((A ∩ B).card : ℝ) - (B.card : ℝ) / n * (A.card : ℝ) := by
  rw [centeredVec, inner_sub_right, inner_smul_right, indicator_inner, indicator_one]

theorem centered_gram {n : ℕ} (hn : n ≠ 0) (A B : Finset (Fin n)) :
    ⟪centeredVec A, centeredVec B⟫_ℝ = ⟪indicatorVec A, centeredVec B⟫_ℝ := by
  have hz : ⟪constantOne n, centeredVec B⟫_ℝ = 0 := by
    rw [real_inner_comm, centered_one hn]
  rw [centeredVec, inner_sub_left, inner_smul_left, hz]
  simp

theorem indicator_disjoint {n : ℕ} {A B : Finset (Fin n)} (h : Disjoint A B) :
    ⟪indicatorVec A, indicatorVec B⟫_ℝ = 0 := by
  rw [indicator_inner, Finset.disjoint_iff_inter_eq_empty.mp h]
  simp

end SimplicialMixingProof

open Finset Matrix
open scoped BigOperators InnerProductSpace Classical
open SimplicialIso.Mixing

namespace SimplicialMixingProof

noncomputable section

theorem indicator_family_inner {n : ℕ} {I : Type*} [DecidableEq I]
    (A : I → Finset (Fin n)) (hA : Pairwise (fun i j => Disjoint (A i) (A j))) (i j : I) :
    ⟪indicatorVec (A i), indicatorVec (A j)⟫_ℝ = if i = j then ((A i).card : ℝ) else 0 := by
  by_cases h : i = j
  · subst j
    rw [indicator_inner]
    simp
  · simp [h, indicator_disjoint (hA h)]

theorem wedge_indicator_norm_sq {n k : ℕ} (A : Fin k → Finset (Fin n))
    (hA : Pairwise (fun i j => Disjoint (A i) (A j))) :
    ‖wedgeForm (fun i => indicatorVec (A i))‖ ^ 2 = ∏ i, ((A i).card : ℝ) := by
  rw [← real_inner_self_eq_norm_sq, wedge_inner]
  have hm : (Matrix.of fun i j => ⟪indicatorVec (A j), indicatorVec (A i)⟫_ℝ) =
      Matrix.diagonal (fun i => ((A i).card : ℝ)) := by
    ext i j
    rw [Matrix.of_apply, indicator_family_inner A hA]
    by_cases h : i = j <;> simp [Matrix.diagonal, h, Ne.symm]
  rw [hm, Matrix.det_diagonal]

theorem wedge_centered_norm_sq_le {n k : ℕ} (hn : n ≠ 0)
    (A : Fin k → Finset (Fin n)) :
    ‖wedgeForm (fun i => centeredVec (A i))‖ ^ 2 ≤
      ‖wedgeForm (fun i => indicatorVec (A i))‖ ^ 2 := by
  have hi : ⟪wedgeForm (fun i => indicatorVec (A i)),
      wedgeForm (fun i => centeredVec (A i))⟫_ℝ =
      ‖wedgeForm (fun i => centeredVec (A i))‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, wedge_inner, wedge_inner]
    congr 1
    ext i j
    exact (centered_gram hn _ _).symm
  have hs := norm_sub_sq_real (wedgeForm (fun i => indicatorVec (A i)))
    (wedgeForm (fun i => centeredVec (A i)))
  nlinarith [sq_nonneg ‖wedgeForm (fun i => indicatorVec (A i)) -
    wedgeForm (fun i => centeredVec (A i))‖]

theorem wedge_prepend_centered {n k : ℕ} (A : Fin k → Finset (Fin n)) :
    wedgeForm (Fin.cons (constantOne n) (fun i => centeredVec (A i))) =
      wedgeForm (Fin.cons (constantOne n) (fun i => indicatorVec (A i))) := by
  ext σ
  rw [wedge_apply, wedge_apply]
  apply Matrix.det_eq_of_forall_row_eq_smul_add_const
    (Fin.cons 0 (fun i => -((A i).card : ℝ) / n)) 0 (by simp)
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i
  · simp
  · simp [centeredVec, sub_eq_add_neg, div_eq_mul_inv, neg_mul]

def leftRows {n k : ℕ} (A : Fin (k+2) → Finset (Fin n)) :
    Fin (k+1) → EuclideanSpace ℝ (Fin n) :=
  Fin.cons (indicatorVec (A 0)) (fun i => indicatorVec (A i.succ.succ))

def rightRows {n k : ℕ} (A : Fin (k+2) → Finset (Fin n)) :
    Fin (k+1) → EuclideanSpace ℝ (Fin n) :=
  Fin.cons (indicatorVec (A 1)) (fun i => indicatorVec (A i.succ.succ))

def centeredRows {n k : ℕ} (A : Fin (k+2) → Finset (Fin n)) :
    Fin (k+1) → EuclideanSpace ℝ (Fin n) :=
  Fin.cons (centeredVec (A 1)) (fun i => centeredVec (A i.succ.succ))

theorem test_cross {n k : ℕ} (A : Fin (k+2) → Finset (Fin n))
    (hA : Pairwise (fun i j => Disjoint (A i) (A j))) (h1 : (A 1).Nonempty) :
    ⟪wedgeForm (leftRows A), wedgeForm (centeredRows A)⟫_ℝ =
      -(∏ i, ((A i).card : ℝ)) / n := by
  rw [wedge_inner]
  have hb : ((A 1).card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr h1
  have hm : (Matrix.of fun i j => ⟪leftRows A j, centeredRows A i⟫_ℝ) =
      centeredGram n (A 0).card (A 1).card (fun i => (A i.succ.succ).card) := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp only [Matrix.of_apply, leftRows, centeredRows, Fin.cons_zero, centeredGram,
          indicator_centered]
        rw [Finset.disjoint_iff_inter_eq_empty.mp (hA (by change (0 : Fin (k+2)) ≠ (0 : Fin (k+1)).succ; exact Ne.symm (Fin.succ_ne_zero _)))]
        simp
      · simp only [Matrix.of_apply, leftRows, centeredRows, Fin.cons_zero, Fin.cons_succ,
          centeredGram, indicator_centered]
        have hj : j.succ.succ ≠ (1 : Fin (k+2)) := by
          change j.succ.succ ≠ (0 : Fin (k+1)).succ
          intro h
          exact Fin.succ_ne_zero j (Fin.succ_inj.mp h)
        rw [Finset.disjoint_iff_inter_eq_empty.mp (hA hj)]
        simp
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp only [Matrix.of_apply, leftRows, centeredRows, Fin.cons_zero, Fin.cons_succ,
          centeredGram, indicator_centered]
        have hi : (0 : Fin (k+2)) ≠ i.succ.succ := Ne.symm (Fin.succ_ne_zero _)
        rw [Finset.disjoint_iff_inter_eq_empty.mp (hA hi)]
        simp [Ne.symm (Fin.succ_ne_zero i)]
      · simp only [Matrix.of_apply, leftRows, centeredRows, Fin.cons_succ,
          centeredGram, indicator_centered, Fin.succ_inj]
        by_cases hij : i = j
        · subst j
          simp
        · rw [Finset.disjoint_iff_inter_eq_empty.mp (hA (by simpa using Ne.symm hij))]
          simp [Ne.symm hij]
  rw [hm, det_centeredGram _ _ _ _ hb, Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [Fin.succ_zero_eq_one]
  ring

end
end SimplicialMixingProof

open Finset
open scoped BigOperators InnerProductSpace

namespace SimplicialMixingProof

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

theorem spectral_norm_bound (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) (ρ : ℝ)
    (hρ : ∀ μ : ℝ, (∃ v : E, v ≠ 0 ∧ T v = μ • v) → |μ| ≤ ρ) :
    0 ≤ ρ ∧ ∀ v, ‖T v‖ ≤ ρ * ‖v‖ := by
  let b := hT.eigenvectorBasis (n := Module.finrank ℝ E) rfl
  let μ := hT.eigenvalues (n := Module.finrank ℝ E) rfl
  have hm (i : Fin (Module.finrank ℝ E)) : |μ i| ≤ ρ := by
    apply hρ
    exact ⟨b i, b.toBasis.ne_zero i, hT.apply_eigenvectorBasis rfl i⟩
  have hr : 0 ≤ ρ := by
    have hp : 0 < Module.finrank ℝ E := Module.finrank_pos
    exact (abs_nonneg (μ ⟨0, hp⟩)).trans (hm ⟨0, hp⟩)
  refine ⟨hr, fun v => ?_⟩
  have hs : ‖T v‖ ^ 2 ≤ (ρ * ‖v‖) ^ 2 := by
    rw [← b.repr.norm_map (T v), ← b.repr.norm_map v,
      EuclideanSpace.real_norm_sq_eq, mul_pow, EuclideanSpace.real_norm_sq_eq,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have he : b.repr (T v) i = μ i * b.repr v i :=
      hT.eigenvectorBasis_apply_self_apply rfl v i
    rw [he, mul_pow]
    have hsq : (μ i)^2 ≤ ρ^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (μ i)) (hm i) 2
    exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  nlinarith [norm_nonneg (T v), norm_nonneg v, mul_nonneg hr (norm_nonneg v)]

end SimplicialMixingProof

open Finset
open scoped BigOperators Classical

namespace SimplicialMixingProof

theorem cyclic_symmetrize (d : ℕ) (c : Fin (d+1) → ℝ) (hc : ∀ i, 0 < c i)
    (D ρ : ℝ) (hD : 0 ≤ D) (hρ : 0 ≤ ρ)
    (hb : ∀ i, D ^ 2 * c i * c (finRotate (d+1) i) ≤
      ρ ^ 2 * (∏ j, c j) ^ 2) :
    D ≤ ρ * (∏ j, c j) ^ ((d : ℝ) / (d+1)) := by
  let P := ∏ j, c j
  have hp : 0 < P := Finset.prod_pos (fun i _ => hc i)
  have hr : (∏ i, c (finRotate (d+1) i)) = P := by
    exact Fintype.prod_equiv (finRotate (d+1)) _ _ (fun _ => rfl)
  have hm := Finset.prod_le_prod
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin (d+1)))) =>
      mul_nonneg (mul_nonneg (sq_nonneg D) (hc i).le) (hc _).le)
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin (d+1)))) => hb i)
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, hr] at hm
  change (D ^ 2) ^ (d+1) * P * P ≤ (ρ ^ 2) ^ (d+1) * (P ^ 2) ^ (d+1) at hm
  have he : (ρ ^ 2) ^ (d+1) * (P ^ 2) ^ (d+1) =
      (ρ ^ (2*(d+1)) * P ^ (2*d)) * P ^ 2 := by
    rw [← pow_mul, ← pow_mul, show 2*(d+1) = 2*d+2 by omega, pow_add P]
    ring
  rw [he] at hm
  have hs : D ^ (2*(d+1)) ≤ ρ ^ (2*(d+1)) * P ^ (2*d) := by
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hp)).mp
    simpa only [pow_mul, pow_two, mul_assoc] using hm
  have hd : (d+1 : ℝ) ≠ 0 := by positivity
  have hrp : (P ^ ((d : ℝ) / (d+1))) ^ (2*(d+1)) = P ^ (2*d) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le, ← Real.rpow_natCast]
    congr 1
    push_cast
    field_simp
  apply (pow_le_pow_iff_left₀ hD (mul_nonneg hρ (Real.rpow_nonneg hp.le _))
    (by omega : 2*(d+1) ≠ 0)).mp
  rwa [mul_pow, hrp]

end SimplicialMixingProof

open Finset Matrix
open scoped BigOperators InnerProductSpace Classical
open SimplicialIso.Mixing

namespace SimplicialMixingProof

noncomputable section

def leftIndex {k : ℕ} : Fin (k+1) → Fin (k+2) :=
  Fin.cons 0 (fun i => i.succ.succ)

theorem leftIndex_injective {k : ℕ} : Function.Injective (leftIndex (k:=k)) := by
  intro i j h
  cases i using Fin.cases <;> cases j using Fin.cases
  · rfl
  · simp only [leftIndex, Fin.cons_zero, Fin.cons_succ] at h
    exact False.elim (Fin.succ_ne_zero _ h.symm)
  · simp only [leftIndex, Fin.cons_zero, Fin.cons_succ] at h
    exact False.elim (Fin.succ_ne_zero _ h)
  · exact Fin.succ_inj.mp h

theorem leftRows_eq {n k : ℕ} (A : Fin (k+2) → Finset (Fin n)) :
    leftRows A = fun i => indicatorVec (A (leftIndex i)) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem rightRows_eq {n k : ℕ} (A : Fin (k+2) → Finset (Fin n)) :
    rightRows A = fun i => indicatorVec (A i.succ) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem centeredRows_eq {n k : ℕ} (A : Fin (k+2) → Finset (Fin n)) :
    centeredRows A = fun i => centeredVec (A i.succ) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem test_left_norm {n k : ℕ} (A : Fin (k+2) → Finset (Fin n))
    (hA : Pairwise (fun i j => Disjoint (A i) (A j))) :
    ‖wedgeForm (leftRows A)‖^2 = (A 0).card * ∏ i : Fin k, ((A i.succ.succ).card : ℝ) := by
  rw [leftRows_eq, wedge_indicator_norm_sq _ (fun i j h => hA (fun he => h (leftIndex_injective he))),
    Fin.prod_univ_succ]
  rfl

theorem test_right_norm {n k : ℕ} (A : Fin (k+2) → Finset (Fin n))
    (hA : Pairwise (fun i j => Disjoint (A i) (A j))) :
    ‖wedgeForm (rightRows A)‖^2 = (A 1).card * ∏ i : Fin k, ((A i.succ.succ).card : ℝ) := by
  rw [rightRows_eq, wedge_indicator_norm_sq _ (fun i j h => hA (fun he => h (Fin.succ_inj.mp he))),
    Fin.prod_univ_succ]
  rfl

theorem test_centered_norm {n k : ℕ} (hn : n ≠ 0)
    (A : Fin (k+2) → Finset (Fin n)) (hA : Pairwise (fun i j => Disjoint (A i) (A j))) :
    ‖wedgeForm (centeredRows A)‖^2 ≤
      (A 1).card * ∏ i : Fin k, ((A i.succ.succ).card : ℝ) := by
  rw [centeredRows_eq]
  calc
    _ ≤ ‖wedgeForm (fun i : Fin (k+1) => indicatorVec (A i.succ))‖^2 :=
      wedge_centered_norm_sq_le hn _
    _ = _ := by rw [← rightRows_eq]; exact test_right_norm A hA

theorem test_centered_cycle {n k : ℕ} (hn : n ≠ 0) (A : Fin (k+2) → Finset (Fin n)) :
    wedgeForm (centeredRows A) ∈ cycles n (k+1) := by
  rw [centeredRows_eq]
  apply wedge_mem_cycles (by omega)
  intro i
  have hh := centered_one hn (A i.succ)
  simpa [PiLp.inner_apply, constantOne, RCLike.inner_apply] using hh

theorem test_centered_cobd {n k : ℕ} (X : Complex n (k+1))
    (A : Fin (k+2) → Finset (Fin n)) :
    cobdTop X (wedgeForm (centeredRows A)) = cobdTop X (wedgeForm (rightRows A)) := by
  rw [centeredRows_eq, rightRows_eq]
  ext τ
  rw [cobdTop_wedge, cobdTop_wedge, wedge_prepend_centered]

theorem cycle_spectral_bound {n d : ℕ} (hd : 1 ≤ d) (X : Complex n d) (α ρ : ℝ)
    (hρ : ∀ μ : ℝ, IsCycleEigenvalue (α • LinearMap.id - upLap X) μ → |μ| ≤ ρ)
    (u : Form n d) (hu : u ∈ cycles n d) (hne : u ≠ 0) :
    0 ≤ ρ ∧ ∀ v : Form n d, v ∈ cycles n d →
      ‖(α • (LinearMap.id : Form n d →ₗ[ℝ] Form n d) - upLap X) v‖ ≤ ρ * ‖v‖ := by
  let K := cycles n d
  let T : Form n d →ₗ[ℝ] Form n d := α • LinearMap.id - upLap X
  have hi : ∀ v ∈ K, T v ∈ K := by
    intro v hv
    exact K.sub_mem (K.smul_mem α hv) (upLap_mem_cycles hd X v)
  have hs : T.IsSymmetric := by
    exact (LinearMap.IsSymmetric.smul (by rfl : star α = α) LinearMap.IsSymmetric.id).sub
      (upLap_isSymmetric X)
  let inst : Nontrivial K := nontrivial_iff_exists_ne (0 : K) |>.mpr
    ⟨⟨u, hu⟩, fun h => hne (congrArg Subtype.val h)⟩
  have hb := spectral_norm_bound (T.restrict hi) (hs.restrict_invariant hi) ρ
    (fun μ hm => by
      obtain ⟨v, hv, he⟩ := hm
      apply hρ μ
      refine ⟨v.val, v.property, ?_, ?_⟩
      · intro hz
        apply hv
        exact Subtype.ext hz
      · exact congrArg Subtype.val he)
  refine ⟨hb.1, fun v hv => ?_⟩
  exact hb.2 ⟨v, hv⟩

end
end SimplicialMixingProof

open Finset
open scoped BigOperators Classical

namespace SimplicialMixingProof

theorem transversal_product {n m : ℕ} (τ : Finset (Fin n)) (hτ : τ.card = m)
    (A : Fin m → Finset (Fin n)) (hA : Pairwise (fun i j => Disjoint (A i) (A j))) :
    (∏ i, ((τ ∩ A i).card : ℝ)) = if (∀ i, (τ ∩ A i).card = 1) then 1 else 0 := by
  have hd : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint (fun i => τ ∩ A i) := by
    intro i _ j _ hij
    exact (hA hij).mono Finset.inter_subset_right Finset.inter_subset_right
  have hu : (Finset.univ.biUnion (fun i : Fin m => τ ∩ A i)) ⊆ τ := by
    intro v hv
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hv
    exact (Finset.mem_inter.mp hi).1
  have hs : (∑ i : Fin m, (τ ∩ A i).card) ≤ m := by
    rw [← Finset.card_biUnion hd]
    exact (Finset.card_le_card hu).trans_eq hτ
  by_cases h : ∀ i, (τ ∩ A i).card = 1
  · simp [h]
  · have hz : ∃ i, (τ ∩ A i).card = 0 := by
      by_contra hz
      push Not at hz
      have hh : ∀ i, 1 ≤ (τ ∩ A i).card := fun i => Nat.one_le_iff_ne_zero.mpr (hz i)
      obtain ⟨i, hi⟩ := not_forall.mp h
      have ht : (∑ _j : Fin m, (1 : ℕ)) < ∑ j : Fin m, (τ ∩ A j).card :=
        Finset.sum_lt_sum (fun j _ => hh j) ⟨i, Finset.mem_univ i, by have := hh i; omega⟩
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at ht
      omega
    rw [if_neg h]
    obtain ⟨i, hi⟩ := hz
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by exact_mod_cast hi)

end SimplicialMixingProof

open Finset Matrix
open scoped BigOperators InnerProductSpace Classical
open SimplicialIso.Mixing

namespace SimplicialMixingProof

noncomputable section

def restrictedVec {n m : ℕ} (τ : Cell n m) (v : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (fun j => v (τ.val.orderEmbOfFin τ.property j))

theorem restricted_inner {n m : ℕ} (τ : Cell n m)
    (u v : EuclideanSpace ℝ (Fin n)) :
    ⟪restrictedVec τ u, restrictedVec τ v⟫_ℝ = ∑ x ∈ τ.val, u x * v x := by
  rw [PiLp.inner_apply]
  change (∑ j, v (τ.val.orderEmbOfFin τ.property j) *
    u (τ.val.orderEmbOfFin τ.property j)) = _
  rw [sum_order τ (fun x => v x * u x)]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem restricted_indicator_one {n m : ℕ} (τ : Cell n m) (A : Finset (Fin n)) :
    ⟪restrictedVec τ (indicatorVec A), restrictedVec τ (constantOne n)⟫_ℝ =
      ((τ.val ∩ A).card : ℝ) := by
  rw [restricted_inner]
  simp [indicatorVec, constantOne]

theorem restricted_indicator_family {n m : ℕ} {I : Type*} [DecidableEq I]
    (τ : Cell n m) (A : I → Finset (Fin n))
    (hA : Pairwise (fun i j => Disjoint (A i) (A j))) (i j : I) :
    ⟪restrictedVec τ (indicatorVec (A i)), restrictedVec τ (indicatorVec (A j))⟫_ℝ =
      if i = j then ((τ.val ∩ A i).card : ℝ) else 0 := by
  by_cases hij : i = j
  · subst j
    rw [restricted_inner]
    simp [indicatorVec]
  · rw [restricted_inner, if_neg hij]
    apply Finset.sum_eq_zero
    intro x _
    have hx : ¬(x ∈ A i ∧ x ∈ A j) := by
      intro h
      exact Finset.disjoint_left.mp (hA hij) h.1 h.2
    by_cases hi : x ∈ A i <;> by_cases hj : x ∈ A j <;> simp_all

theorem restricted_one_inner {n m : ℕ} (τ : Cell n m) :
    ⟪restrictedVec τ (constantOne n), restrictedVec τ (constantOne n)⟫_ℝ = (m : ℝ) := by
  rw [restricted_inner]
  simp [constantOne, τ.property]

theorem top_wedge_product {n k : ℕ} (τ : Cell n (k+2))
    (A : Fin (k+2) → Finset (Fin n))
    (hA : Pairwise (fun i j => Disjoint (A i) (A j))) :
    wedgeForm (Fin.cons (constantOne n) (rightRows A)) τ *
      wedgeForm (Fin.cons (constantOne n) (leftRows A)) τ =
      -(∏ i, ((τ.val ∩ A i).card : ℝ)) := by
  let rv : Fin (k+2) → EuclideanSpace ℝ (Fin n) := Fin.cons (constantOne n) (rightRows A)
  let lv : Fin (k+2) → EuclideanSpace ℝ (Fin n) := Fin.cons (constantOne n) (leftRows A)
  let R : Matrix (Fin (k+2)) (Fin (k+2)) ℝ :=
    fun i j => rv i (τ.val.orderEmbOfFin τ.property j)
  let L : Matrix (Fin (k+2)) (Fin (k+2)) ℝ :=
    fun i j => lv i (τ.val.orderEmbOfFin τ.property j)
  have hm : R * L.transpose = topCrossGram (k+2) (τ.val ∩ A 0).card
      (τ.val ∩ A 1).card (fun i => (τ.val ∩ A i.succ.succ).card) := by
    have he (i j : Fin (k+2)) : (R * L.transpose) i j =
        ⟪restrictedVec τ (rv i),
          restrictedVec τ (lv j)⟫_ℝ := by
      rw [Matrix.mul_apply, PiLp.inner_apply]
      change (∑ l, R i l * L j l) = ∑ l, L j l * R i l
      apply Finset.sum_congr rfl
      intro l _
      ring
    ext i j
    rw [he]
    dsimp only [rv, lv]
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · change ⟪restrictedVec τ (constantOne n), restrictedVec τ (constantOne n)⟫_ℝ = (k+2 : ℝ)
        simpa only [Nat.cast_add, Nat.cast_ofNat] using restricted_one_inner τ
      · refine Fin.cases ?_ (fun j => ?_) j <;>
          (simp only [topCrossGram, leftRows, Fin.cons_zero, Fin.cons_succ];
           exact (real_inner_comm _ _).trans (restricted_indicator_one τ _))
    · refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j => ?_) j
        · simp [topCrossGram, rightRows, restricted_indicator_one]
        · refine Fin.cases ?_ (fun j => ?_) j
          · simp [topCrossGram, leftRows, rightRows, restricted_indicator_family τ A hA]
          · have hj : (1 : Fin (k+2)) ≠ j.succ.succ := by
              change (0 : Fin (k+1)).succ ≠ j.succ.succ
              exact fun h => Fin.succ_ne_zero j (Fin.succ_inj.mp h).symm
            simp [topCrossGram, leftRows, rightRows, restricted_indicator_family τ A hA, hj]
      · refine Fin.cases ?_ (fun j => ?_) j
        · simp [topCrossGram, rightRows, restricted_indicator_one]
        · refine Fin.cases ?_ (fun j => ?_) j <;>
            simp [topCrossGram, leftRows, rightRows, restricted_indicator_family τ A hA]
  rw [wedge_apply, wedge_apply]
  change R.det * L.det = _
  rw [← Matrix.det_transpose L, ← Matrix.det_mul, hm, det_topCrossGram]
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [Fin.succ_zero_eq_one]
  ring


theorem test_top_pairing {n k : ℕ} (X : Complex n (k+1))
    (A : Fin (k+2) → Finset (Fin n))
    (hA : Pairwise (fun i j => Disjoint (A i) (A j))) :
    ⟪wedgeForm (leftRows A), upLap X (wedgeForm (rightRows A))⟫_ℝ =
      -((F X A).card : ℝ) := by
  have hp (τ : Cell n (k+2)) :
      cobdTop X (wedgeForm (rightRows A)) τ * cobdTop X (wedgeForm (leftRows A)) τ =
        -(if τ.val ∈ F X A then (1 : ℝ) else 0) := by
    rw [cobdTop_wedge, cobdTop_wedge]
    by_cases ht : τ.val ∈ X.top
    · rw [if_pos ht, if_pos ht, top_wedge_product τ A hA,
        transversal_product τ.val τ.property A hA]
      simp only [F, Finset.mem_filter, ht, true_and]
    · simp [ht, F]
  have hc : (Finset.univ.filter (fun τ : Cell n (k+2) => τ.val ∈ F X A)).card =
      (F X A).card := by
    apply Finset.card_bij (fun τ _ => τ.val)
    · intro τ hτ
      exact (Finset.mem_filter.mp hτ).2
    · intro τ _ σ _ h
      exact Subtype.ext h
    · intro τ hτ
      have ht := X.card_top τ (Finset.mem_filter.mp hτ).1
      exact ⟨⟨τ, ht⟩, by simp [hτ], rfl⟩
  rw [real_inner_comm]
  change ⟪bdTop X (cobdTop X (wedgeForm (rightRows A))), wedgeForm (leftRows A)⟫_ℝ = _
  rw [inner_bdTop, PiLp.inner_apply]
  change (∑ τ : Cell n (k+2), cobdTop X (wedgeForm (leftRows A)) τ *
    cobdTop X (wedgeForm (rightRows A)) τ) = _
  have hp' (τ : Cell n (k+2)) :
      cobdTop X (wedgeForm (leftRows A)) τ * cobdTop X (wedgeForm (rightRows A)) τ =
        -(if τ.val ∈ F X A then (1 : ℝ) else 0) := (mul_comm _ _).trans (hp τ)
  simp_rw [hp']
  rw [Finset.sum_neg_distrib]
  congr 1
  simpa only [Finset.sum_boole] using congrArg (fun t : ℕ => (t : ℝ)) hc

end
end SimplicialMixingProof

open Finset Matrix
open scoped BigOperators InnerProductSpace Classical
open SimplicialIso.Mixing

namespace SimplicialMixingProof

noncomputable section

theorem asymmetric_squared {n k : ℕ} (X : Complex n (k+1)) (α ρ : ℝ)
    (A : Fin (k+2) → Finset (Fin n))
    (hA : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hpos : ∀ i, (A i).Nonempty)
    (hρ : ∀ μ : ℝ, IsCycleEigenvalue (α • LinearMap.id - upLap X) μ → |μ| ≤ ρ) :
    0 ≤ ρ ∧
      |((F X A).card : ℝ) - α * (∏ i, ((A i).card : ℝ)) / n|^2 *
        (A 0).card * (A 1).card ≤ ρ^2 * (∏ i, ((A i).card : ℝ))^2 := by
  have hn : n ≠ 0 := by
    obtain ⟨v, _⟩ := hpos 0
    exact Nat.ne_of_gt (Nat.zero_lt_of_lt v.isLt)
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  let P : ℝ := ∏ i, ((A i).card : ℝ)
  let C : ℝ := ∏ i : Fin k, ((A i.succ.succ).card : ℝ)
  have hp : 0 < P := Finset.prod_pos (fun i _ => by exact_mod_cast (hpos i).card_pos)
  have hprod : P = (A 0).card * (A 1).card * C := by
    dsimp [P, C]
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    simp only [Fin.succ_zero_eq_one]
    ring
  let φ := wedgeForm (leftRows A)
  let ψ := wedgeForm (rightRows A)
  let ζ := wedgeForm (centeredRows A)
  let T : Form n (k+1) →ₗ[ℝ] Form n (k+1) := α • LinearMap.id - upLap X
  have hz : ζ ∈ cycles n (k+1) := test_centered_cycle hn A
  have hcross : ⟪φ, ζ⟫_ℝ = -P/n := test_cross A hA (hpos 1)
  have hne : ζ ≠ 0 := by
    intro he
    rw [he, inner_zero_right] at hcross
    exact (div_ne_zero (neg_ne_zero.mpr hp.ne') hnr) hcross.symm
  have hs := cycle_spectral_bound (by omega) X α ρ hρ ζ hz hne
  have htop : upLap X ζ = upLap X ψ := by
    exact congrArg (bdTop X) (test_centered_cobd X A)
  have hid : ⟪φ, T ζ⟫_ℝ = ((F X A).card : ℝ) - α*P/n := by
    change ⟪φ, α • ζ - upLap X ζ⟫_ℝ = _
    rw [inner_sub_right, inner_smul_right, htop, hcross, test_top_pairing X A hA]
    ring
  have hphi : ‖φ‖^2 = (A 0).card*C := test_left_norm A hA
  have hzet : ‖ζ‖^2 ≤ (A 1).card*C := test_centered_norm hn A hA
  have hcs : |⟪φ, T ζ⟫_ℝ| ≤ ‖φ‖ * (ρ * ‖ζ‖) :=
    (abs_real_inner_le_norm φ (T ζ)).trans
      (mul_le_mul_of_nonneg_left (hs.2 ζ hz) (norm_nonneg φ))
  have hb : |((F X A).card : ℝ)-α*P/n|^2 ≤
      ρ^2*((A 0).card*C)*((A 1).card*C) := by
    calc
      _ = |⟪φ, T ζ⟫_ℝ|^2 := by rw [hid]
      _ ≤ (‖φ‖*(ρ*‖ζ‖))^2 := pow_le_pow_left₀ (abs_nonneg _) hcs 2
      _ = ρ^2*((A 0).card*C)*‖ζ‖^2 := by rw [mul_pow, mul_pow, hphi]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hzet (by positivity)
  refine ⟨hs.1, ?_⟩
  have hh := mul_le_mul_of_nonneg_right hb
    (show (0 : ℝ) ≤ (A 0).card * (A 1).card by positivity)
  change |((F X A).card : ℝ)-α*P/n|^2 * (A 0).card * (A 1).card ≤ ρ^2*P^2
  rw [hprod] at hh ⊢
  nlinarith only [hh]

end
end SimplicialMixingProof

namespace SimplicialIso.Mixing

open Finset
open scoped InnerProductSpace

/-- Theorem (1.4), p. 16 (the Mixing Lemma, precise form): for a `d`-complex `X` with a complete
skeleton, `α ∈ ℝ`, disjoint vertex sets `A_0, …, A_d` (not necessarily a partition), and any `ρ`
bounding the absolute value of every eigenvalue of `αI − Δ⁺` on `Z_{d-1}` (in particular
`ρ = ρ_α = ‖(αI − Δ⁺)|_{Z_{d-1}}‖`),
`| |F(A_0, …, A_d)| − α |A_0| ⋯ |A_d| / n | ≤ ρ (|A_0| ⋯ |A_d|)^{d/(d+1)}`. -/
theorem theorem_1_4 (n d : ℕ) (hd : 1 ≤ d) (X : Complex n d) (α : ℝ)
    (A : Fin (d + 1) → Finset (Fin n)) (hA : Pairwise (fun i j => Disjoint (A i) (A j))) (ρ : ℝ)
    (hρ : ∀ μ, IsCycleEigenvalue (α • LinearMap.id - upLap X) μ → |μ| ≤ ρ) :
    |((F X A).card : ℝ) - α * (∏ i, ((A i).card : ℝ)) / n| ≤
      ρ * (∏ i, ((A i).card : ℝ)) ^ ((d : ℝ) / (d + 1)) := by
  classical
  by_cases hpos : ∀ i, (A i).Nonempty
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
    have hb := SimplicialMixingProof.asymmetric_squared X α ρ A hA hpos hρ
    apply SimplicialMixingProof.cyclic_symmetrize (k+1) (fun i => ((A i).card : ℝ))
      (fun i => by exact_mod_cast (hpos i).card_pos) _ ρ (abs_nonneg _) hb.1
    intro i
    let B : Fin (k+2) → Finset (Fin n) := fun j => A (i+j)
    have hB : Pairwise (fun j l => Disjoint (B j) (B l)) := by
      intro j l hjl
      exact hA (fun he => hjl (add_left_cancel he))
    have hF : F X B = F X A := by
      apply Finset.filter_congr
      intro τ _
      constructor
      · intro h j
        obtain ⟨l, hl⟩ := (Equiv.addLeft i).surjective j
        rw [← hl]
        exact h l
      · intro h j
        exact h (i+j)
    have hp : (∏ j, ((B j).card : ℝ)) = ∏ j, ((A j).card : ℝ) :=
      Fintype.prod_equiv (Equiv.addLeft i) _ _ (fun _ => rfl)
    have hh := (SimplicialMixingProof.asymmetric_squared X α ρ B hB
      (fun j => hpos (i+j)) hρ).2
    rw [hF, hp] at hh
    simpa only [B, add_zero, finRotate_apply] using hh
  · push Not at hpos
    obtain ⟨i, hi⟩ := hpos
    have he : A i = ∅ := hi
    have hp : (∏ j, ((A j).card : ℝ)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [he]
    have hF : F X A = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro τ hτ
      have ht := (Finset.mem_filter.mp hτ).2 i
      simp [he] at ht
    have hdpos : (0 : ℝ) < (d : ℝ)/(d+1) := div_pos (by exact_mod_cast (Nat.zero_lt_of_lt hd)) (by positivity)
    simp [hF, hp, Real.zero_rpow hdpos.ne']

end SimplicialIso.Mixing

open SimplicialIso.Mixing
theorem solution (n d : ℕ) (hd : 1 ≤ d) (X : Complex n d) (α : ℝ)
    (A : Fin (d + 1) → Finset (Fin n)) (hA : Pairwise (fun i j => Disjoint (A i) (A j))) (ρ : ℝ)
    (hρ : ∀ μ, IsCycleEigenvalue (α • LinearMap.id - upLap X) μ → |μ| ≤ ρ) :
    |((F X A).card : ℝ) - α * (∏ i, ((A i).card : ℝ)) / n| ≤
      ρ * (∏ i, ((A i).card : ℝ)) ^ ((d : ℝ) / (d + 1)) :=
  SimplicialIso.Mixing.theorem_1_4 n d hd X α A hA ρ hρ
