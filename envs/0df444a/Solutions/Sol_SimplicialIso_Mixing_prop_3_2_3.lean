-- Prove2me | solution 1 for SimplicialIso.Mixing.prop_3_2_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T05:42:05.849343+00:00
-- url     : https://prove2.me/submissions/4a3bac44-ecb4-459d-9eec-03a84b207d28

import Mathlib
import Definitions.Def_SimplicialIso_Mixing_Setting

/- Supporting proof from sometik179, accepted submission ffdcaf50-1fb5-4373-992c-4a96d8738b90; unused cyclic symmetrization omitted. -/
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

namespace SimplicialMixingProof
@[simp] theorem one_inner_one (n : ℕ) :
    ⟪constantOne n, constantOne n⟫_ℝ = (n : ℝ) := by
  rw [PiLp.inner_apply]
  simp [constantOne]
end SimplicialMixingProof


set_option backward.isDefEq.respectTransparency false

open Finset SimplicialIso.Mixing SimplicialMixingProof
open scoped InnerProductSpace

noncomputable section

namespace SimplicialProjectionSplit

lemma exact_orthogonal (n d : ℕ) (hd : 1 ≤ d) : exact n d = (cycles n d)ᗮ := by
  cases d with
  | zero => omega
  | succ k =>
    have hadj : cobdLow n (k + 1) = (bdLow n (k + 1)).adjoint := by
      apply (LinearMap.eq_adjoint_iff _ _).2
      intro f g
      rw [real_inner_comm, ← inner_bdLow, real_inner_comm]
    rw [exact, cycles, LinearMap.orthogonal_ker, hadj]

lemma projection_add (n d : ℕ) (hd : 1 ≤ d) (f : Form n d) :
    projExact n d f + projCycles n d f = f := by
  unfold projExact projCycles
  simp only [exact_orthogonal n d hd, Submodule.starProjection_orthogonal_val]
  exact sub_add_cancel _ _

lemma upLap_projExact (n d : ℕ) (hd : 1 ≤ d) (X : Complex n d) (f : Form n d) :
    upLap X (projExact n d f) = 0 := by
  have hm : projExact n d f ∈ exact n d := (exact n d).starProjection_apply_mem f
  obtain ⟨g, hg⟩ := hm
  rw [← hg]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  change bdTop X (cobdTop X (cobdLow n (k + 1) g)) = 0
  rw [cobdTop_cobdLow, map_zero]

end SimplicialProjectionSplit



set_option backward.isDefEq.respectTransparency false

open Finset Matrix SimplicialIso.Mixing SimplicialMixingProof SimplicialProjectionSplit
open scoped InnerProductSpace

noncomputable section

namespace SimplicialLowerLaplacian

def center {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  v - (⟪v, constantOne n⟫_ℝ / n) • constantOne n

lemma center_orthogonal {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) :
    ⟪center v, constantOne n⟫_ℝ = 0 := by
  by_cases hn : n = 0
  · subst n
    have he : constantOne 0 = 0 := by ext i; exact Fin.elim0 i
    simp [he]
  · rw [center, inner_sub_left, inner_smul_left, one_inner_one]
    have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    simp only [starRingEnd_apply, star_trivial]
    field_simp
    ring

lemma prepend_center {n k : ℕ} (v : Fin k → EuclideanSpace ℝ (Fin n)) :
    wedgeForm (Fin.cons (constantOne n) (fun i => center (v i))) =
      wedgeForm (Fin.cons (constantOne n) v) := by
  ext σ
  rw [wedge_apply, wedge_apply]
  apply Matrix.det_eq_of_forall_row_eq_smul_add_const
    (Fin.cons 0 (fun i => -⟪v i, constantOne n⟫_ℝ / n)) 0 (by simp)
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i
  · simp
  · simp [center, sub_eq_add_neg, div_eq_mul_inv, neg_mul]

lemma bdLow_prepend {n k : ℕ} (v : Fin k → EuclideanSpace ℝ (Fin n))
    (hv : ∀ i, ⟪v i, constantOne n⟫_ℝ = 0) :
    bdLow n (k + 1) (wedgeForm (Fin.cons (constantOne n) v)) =
      (n : ℝ) • wedgeForm v := by
  have h : innerₗ (Form n k) (bdLow n (k + 1) (wedgeForm (Fin.cons (constantOne n) v))) =
      innerₗ (Form n k) ((n : ℝ) • wedgeForm v) := by
    apply LinearMap.ext_on (wedge_span n k)
    rintro _ ⟨w, rfl⟩
    change ⟪bdLow n (k + 1) (wedgeForm (Fin.cons (constantOne n) v)), wedgeForm w⟫_ℝ = _
    rw [inner_bdLow, cobdLow_wedge]
    change ⟪wedgeForm (Fin.cons (constantOne n) v), wedgeForm (Fin.cons (constantOne n) w)⟫_ℝ =
      ⟪(n : ℝ) • wedgeForm v, wedgeForm w⟫_ℝ
    rw [inner_smul_left, wedge_inner, wedge_inner, Matrix.det_succ_row_zero,
      Fin.sum_univ_succ]
    simp only [Matrix.of_apply, Fin.cons_zero, Fin.cons_succ, hv, mul_zero, zero_mul,
      Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero, one_mul,
      one_inner_one, Fin.succAbove_zero]
    rfl
  exact ext_inner_right ℝ (fun w => LinearMap.congr_fun h w)

lemma lowLap_cobdLow (n k : ℕ) (f : Form n k) :
    lowLap n (k + 1) (cobdLow n (k + 1) f) = (n : ℝ) • cobdLow n (k + 1) f := by
  have h : (lowLap n (k + 1)).comp (cobdLow n (k + 1)) =
      (n : ℝ) • cobdLow n (k + 1) := by
    apply LinearMap.ext_on (wedge_span n k)
    rintro _ ⟨v, rfl⟩
    change cobdLow n (k + 1) (bdLow n (k + 1) (cobdLow n (k + 1) (wedgeForm v))) =
      (n : ℝ) • cobdLow n (k + 1) (wedgeForm v)
    rw [cobdLow_wedge, ← prepend_center v, bdLow_prepend _ (fun i => center_orthogonal (v i)),
      map_smul, cobdLow_wedge]
  exact LinearMap.congr_fun h f

lemma lowLap_exact (n d : ℕ) (hd : 1 ≤ d) (f : Form n d) (hf : f ∈ exact n d) :
    lowLap n d f = (n : ℝ) • f := by
  obtain ⟨g, rfl⟩ := hf
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  exact lowLap_cobdLow n k g

lemma lowLap_cycle (n d : ℕ) (f : Form n d) (hf : f ∈ cycles n d) :
    lowLap n d f = 0 := by
  change bdLow n d f = 0 at hf
  change cobdLow n d (bdLow n d f) = 0
  rw [hf, map_zero]

end SimplicialLowerLaplacian

theorem solution (n d : ℕ) (hd : 1 ≤ d) (f : Form n d) :
    lowLap n d f = (n : ℝ) • projExact n d f := by
  conv_lhs => rw [← projection_add n d hd f]
  have he := SimplicialLowerLaplacian.lowLap_exact n d hd (projExact n d f)
    ((exact n d).starProjection_apply_mem f)
  have hc := SimplicialLowerLaplacian.lowLap_cycle n d (projCycles n d f)
    ((cycles n d).starProjection_apply_mem f)
  rw [map_add, he, hc, add_zero]


#print axioms solution
