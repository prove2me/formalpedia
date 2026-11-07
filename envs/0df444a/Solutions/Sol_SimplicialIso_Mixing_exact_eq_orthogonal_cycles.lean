-- Prove2me | solution 1 for SimplicialIso.Mixing.exact_eq_orthogonal_cycles
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T04:15:32.263027+00:00
-- url     : https://prove2.me/submissions/1bfb7ce3-9a40-4a23-9568-e33f5ce030c6

import Definitions.Def_SimplicialIso_Mixing_Setting

/- Incidence reindexing adapted from sometik179's accepted proof of the Mixing Lemma,
   Prove2Me submission ffdcaf50-1fb5-4373-992c-4a96d8738b90. -/
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

theorem solution (n d : ℕ) (hd : 1 ≤ d) :
    exact n d = (cycles n d)ᗮ := by
  cases d with
  | zero => omega
  | succ k =>
    have hadj : cobdLow n (k + 1) = (bdLow n (k + 1)).adjoint := by
      apply (LinearMap.eq_adjoint_iff _ _).2
      intro f g
      rw [real_inner_comm, ← SimplicialMixingProof.inner_bdLow, real_inner_comm]
    rw [exact, cycles, LinearMap.orthogonal_ker, hadj]

#print axioms solution
