-- Prove2me | solution 1 for QuantumMaxCutEnergy.exists_matching_ge_color_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T03:25:21.549542+00:00
-- url     : https://prove2.me/submissions/20e1ac1e-9121-4115-9685-b5669b5aa5df

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEdgeLoads
import Definitions.Def_QuantumMaxCutMatchingPadding
import Mathlib

set_option autoImplicit false
open scoped BigOperators

open QuantumMaxCutEnergy

/-- A nonzero pair weight joins different colours. -/
lemma color_ne_of_pairWeight_ne {n : ℕ} (x : Edge n → ℝ) (c : Fin n → Bool)
    (hc : ∀ e : Edge n, c e.val.1 ≠ c e.val.2) {a b : Fin n}
    (h : pairWeight x a b ≠ 0) : c a ≠ c b := by
  unfold pairWeight at h
  by_cases hlt : a < b
  · rw [dif_pos hlt] at h
    exact hc ⟨(a, b), hlt⟩
  · by_cases hgt : b < a
    · rw [dif_neg hlt, dif_pos hgt] at h
      exact fun hcon => hc ⟨(b, a), hgt⟩ hcon.symm
    · rw [dif_neg hlt, dif_neg hgt] at h
      exact absurd rfl h

/-- The edge spanned by the nontrivial step `a ↦ σ a`. -/
def stepEdge {n : ℕ} (σ : Equiv.Perm (Fin n)) (a : Fin n) (h : σ a ≠ a) : Edge n :=
  if hlt : a < σ a then ⟨(a, σ a), hlt⟩ else ⟨(σ a, a), by show σ a < a; omega⟩

lemma stepEdge_endpoints {n : ℕ} (σ : Equiv.Perm (Fin n)) (a : Fin n) (h : σ a ≠ a) :
    ((stepEdge σ a h).val.1 = a ∧ (stepEdge σ a h).val.2 = σ a) ∨
      ((stepEdge σ a h).val.1 = σ a ∧ (stepEdge σ a h).val.2 = a) := by
  unfold stepEdge
  split_ifs with hlt
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

lemma stepEdge_endpoint_of {n : ℕ} (σ : Equiv.Perm (Fin n)) (a : Fin n) (h : σ a ≠ a)
    {v : Fin n} (hv : (stepEdge σ a h).val.1 = v ∨ (stepEdge σ a h).val.2 = v) :
    v = a ∨ v = σ a := by
  rcases stepEdge_endpoints σ a h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases hv with hv | hv
    · exact Or.inl (by rw [← hv, h1])
    · exact Or.inr (by rw [← hv, h2])
  · rcases hv with hv | hv
    · exact Or.inr (by rw [← hv, h1])
    · exact Or.inl (by rw [← hv, h2])

lemma pairWeight_stepEdge {n : ℕ} (w : Edge n → ℝ) (σ : Equiv.Perm (Fin n)) (a : Fin n)
    (h : σ a ≠ a) : pairWeight w a (σ a) = w (stepEdge σ a h) := by
  by_cases hlt : a < σ a
  · have he : stepEdge σ a h = ⟨(a, σ a), hlt⟩ := by
      unfold stepEdge; rw [dif_pos hlt]
    rw [he, pairWeight, dif_pos hlt]
  · have hgt : σ a < a := by omega
    have he : stepEdge σ a h = ⟨(σ a, a), hgt⟩ := by
      unfold stepEdge; rw [dif_neg hlt]
    rw [he, pairWeight, dif_neg hlt, dif_pos hgt]

/-- The steps of a permutation that start in one colour class form a matching of the same total weight. -/
theorem solution {n : ℕ} (w : Edge n → ℝ) (x : Edge n → ℝ)
    (c : Fin n → Bool) (hc : ∀ e : Edge n, c e.val.1 ≠ c e.val.2)
    (σ : Equiv.Perm (Fin n)) (b : Bool)
    (hne : ∀ a, σ a ≠ a → pairWeight x a (σ a) ≠ 0) :
    ∃ M : Finset (Edge n),
      (∀ e ∈ M, ∀ e' ∈ M, e ≠ e' →
        e.val.1 ≠ e'.val.1 ∧ e.val.1 ≠ e'.val.2 ∧ e.val.2 ≠ e'.val.1 ∧ e.val.2 ≠ e'.val.2) ∧
      (∑ a ∈ Finset.univ.filter (fun a : Fin n => c a = b ∧ σ a ≠ a), pairWeight w a (σ a))
        ≤ ∑ e ∈ M, w e := by
  classical
  set S : Finset (Fin n) := Finset.univ.filter (fun a : Fin n => c a = b ∧ σ a ≠ a) with hS
  have hS_mem : ∀ a : Fin n, a ∈ S ↔ c a = b ∧ σ a ≠ a := by
    intro a; rw [hS, Finset.mem_filter]; simp
  have hstep : ∀ a : {a : Fin n // a ∈ S}, σ a.val ≠ a.val :=
    fun a => (hS_mem a.val).mp a.property |>.2
  have hstep' : ∀ (a : Fin n) (ha : a ∈ S), σ a ≠ a := fun a ha => (hS_mem a).mp ha |>.2
  set φ : {a : Fin n // a ∈ S} → Edge n := fun a => stepEdge σ a.val (hstep a) with hφ
  -- colour facts
  have hcol : ∀ a : {a : Fin n // a ∈ S}, c a.val = b ∧ c (σ a.val) ≠ b := by
    intro a
    have hb : c a.val = b := (hS_mem a.val).mp a.property |>.1
    refine ⟨hb, ?_⟩
    have h1 : pairWeight x a.val (σ a.val) ≠ 0 := hne a.val (hstep a)
    have h2 : c a.val ≠ c (σ a.val) := color_ne_of_pairWeight_ne x c hc h1
    rw [hb] at h2
    exact Ne.symm h2
  -- injectivity of `φ` on the attached set
  have hinj : Set.InjOn φ ↑(Finset.univ : Finset {a : Fin n // a ∈ S}) := by
    intro a _ a' _ heq
    have ea := stepEdge_endpoints σ a.val (hstep a)
    have ea' := stepEdge_endpoints σ a'.val (hstep a')
    have hend1 : (φ a).val.1 = a.val ∨ (φ a).val.2 = a.val := by
      rw [hφ]; simp only
      rcases ea with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact Or.inl e1
      · exact Or.inr e2
    have hend2 : (φ a).val.1 = σ a.val ∨ (φ a).val.2 = σ a.val := by
      rw [hφ]; simp only
      rcases ea with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact Or.inr e2
      · exact Or.inl e1
    rw [heq] at hend1 hend2
    have h1' := stepEdge_endpoint_of σ a'.val (hstep a') hend1
    have h2' := stepEdge_endpoint_of σ a'.val (hstep a') hend2
    obtain ⟨ha, hsa⟩ := hcol a
    obtain ⟨ha', hsa'⟩ := hcol a'
    rcases h1' with h1' | h1'
    · rcases h2' with h2' | h2'
      · exfalso
        exact hsa (by rw [h2']; exact ha')
      · exact Subtype.ext h1'
    · rcases h2' with h2' | h2'
      · exfalso
        exact hsa' (by rw [← h1']; exact ha)
      · exfalso
        exact hstep a (by rw [h2', ← h1'])
  refine ⟨(Finset.univ : Finset {a : Fin n // a ∈ S}).image φ, ?_, ?_⟩
  · -- the matching property
    intro e he e' he' hne'
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨a', -, rfl⟩ := Finset.mem_image.mp he'
    obtain ⟨ha, hsa⟩ := hcol a
    obtain ⟨ha', hsa'⟩ := hcol a'
    have haa' : a ≠ a' := by
      intro h; subst h; exact hne' rfl
    have noshare : ∀ v : Fin n,
        ¬(((φ a).val.1 = v ∨ (φ a).val.2 = v) ∧ ((φ a').val.1 = v ∨ (φ a').val.2 = v)) := by
      intro v hv
      obtain ⟨hv1, hv2⟩ := hv
      have e1 := stepEdge_endpoint_of σ a.val (hstep a) hv1
      have e2 := stepEdge_endpoint_of σ a'.val (hstep a') hv2
      rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2
      · exact haa' (Subtype.ext (e1 ▸ e2))
      · exact hsa' (by rw [← e2, e1]; exact ha)
      · exact hsa (by rw [← e1, e2]; exact ha')
      · exact haa' (Subtype.ext (σ.injective (by rw [← e1, ← e2])))
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h
      exact noshare _ ⟨Or.inl rfl, Or.inl h.symm⟩
    · intro h
      exact noshare _ ⟨Or.inl rfl, Or.inr h.symm⟩
    · intro h
      exact noshare _ ⟨Or.inr rfl, Or.inl h.symm⟩
    · intro h
      exact noshare _ ⟨Or.inr rfl, Or.inr h.symm⟩
  · -- the sum comparison
    have hsum1 : (∑ e ∈ (Finset.univ : Finset {a : Fin n // a ∈ S}).image φ, w e)
        = ∑ a : {a : Fin n // a ∈ S}, w (φ a) :=
      @Finset.sum_image (Edge n) {a : Fin n // a ∈ S} ℝ _ w _ (Finset.univ) φ hinj
    rw [hsum1, ← Finset.sum_coe_sort S (fun a => pairWeight w a (σ a))]
    exact Finset.sum_le_sum (fun a _ => le_of_eq (pairWeight_stepEdge w σ a.val (hstep a)))


#print axioms solution
