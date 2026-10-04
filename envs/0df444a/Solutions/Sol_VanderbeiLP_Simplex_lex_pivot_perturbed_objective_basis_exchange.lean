-- Prove2me | solution 1 for VanderbeiLP.Simplex.lex_pivot_perturbed_objective_basis_exchange
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T23:21:55.482334+00:00
-- url     : https://prove2.me/submissions/af2052ca-1a4f-494c-8e03-0c5e2d7c3946

import Mathlib
import Definitions.Def_VanderbeiLP_Simplex_PivotRules

set_option autoImplicit false

namespace P2M9d2868df

open VanderbeiLP.Simplex

variable {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}

/-- Coordinates of `v` in the basic columns of `D`, extended by `0`. -/
noncomputable def rr (D : Dictionary A) (v : Fin m → ℝ) (i : Fin (n + m)) : ℝ :=
  if h : i ∈ D.B then D.colBasis.repr v ⟨i, h⟩ else 0

lemma colBasis_apply (D : Dictionary A) (j : D.B) :
    D.colBasis j = augCol A (j : Fin (n + m)) := by
  unfold Dictionary.colBasis
  rw [coe_basisOfLinearIndependentOfCardEqFinrank']

lemma sum_rr (D : Dictionary A) (v : Fin m → ℝ) :
    ∑ i ∈ D.B, rr D v i • augCol A i = v := by
  conv_rhs => rw [← D.colBasis.sum_repr v]
  rw [← Finset.sum_coe_sort D.B]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [colBasis_apply]
  simp [rr, j.2]

lemma rr_eq_of_sum (D : Dictionary A) (w : Fin (n + m) → ℝ) (v : Fin m → ℝ)
    (hw : ∑ i ∈ D.B, w i • augCol A i = v) : ∀ i ∈ D.B, rr D v i = w i := by
  intro i hi
  have hv : v = ∑ j : D.B, w j • D.colBasis j := by
    rw [← hw, ← Finset.sum_coe_sort D.B]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [colBasis_apply]
  simp only [rr, dif_pos hi]
  rw [hv]
  exact congrFun (D.colBasis.repr_sum_self (fun j : D.B => w j)) ⟨i, hi⟩

lemma abar_eq (D : Dictionary A) (i j : Fin (n + m)) :
    D.abar i j = rr D (augCol A j) i := rfl

lemma bbar_eq (D : Dictionary A) (b : Fin m → ℝ) (i : Fin (n + m)) :
    D.bbar b i = rr D b i := rfl

lemma rr_exchange (D D' : Dictionary A) (k l : Fin (n + m)) (hk : k ∉ D.B) (hl : l ∈ D.B)
    (hlk : D.abar l k ≠ 0) (hB : D'.B = insert k (D.B.erase l)) (v : Fin m → ℝ) :
    ∀ i ∈ D'.B, rr D' v i = (if i = k then rr D v l / D.abar l k
      else rr D v i - D.abar i k * (rr D v l / D.abar l k)) := by
  apply rr_eq_of_sum
  have hknot : k ∉ D.B.erase l := fun h => hk (Finset.mem_of_mem_erase h)
  rw [hB, Finset.sum_insert hknot, if_pos rfl]
  rw [Finset.sum_congr rfl (fun i hi => by
    rw [if_neg (fun h : i = k => hknot (h ▸ hi))])]
  set t := rr D v l / D.abar l k with ht
  have hta : t * D.abar l k = rr D v l := by rw [ht]; field_simp
  have hcol := sum_rr D (augCol A k)
  have hv := sum_rr D v
  rw [← Finset.add_sum_erase _ _ hl] at hcol hv
  simp only [← abar_eq] at hcol
  have e1 : ∑ i ∈ D.B.erase l, (rr D v i - D.abar i k * t) • augCol A i =
      ∑ i ∈ D.B.erase l, rr D v i • augCol A i -
        t • ∑ i ∈ D.B.erase l, D.abar i k • augCol A i := by
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sub_smul, mul_comm, mul_smul]
  rw [e1]
  have h1 : ∑ i ∈ D.B.erase l, D.abar i k • augCol A i =
      augCol A k - D.abar l k • augCol A l := by rw [← hcol]; abel
  have h2 : ∑ i ∈ D.B.erase l, rr D v i • augCol A i = v - rr D v l • augCol A l := by
    rw [eq_sub_iff_add_eq, add_comm]; exact hv
  rw [h1, h2, smul_sub, smul_smul, hta]
  abel

lemma scalar_identity (D D' : Dictionary A) (c : Fin n → ℝ) (k l : Fin (n + m))
    (hk : k ∉ D.B) (hl : l ∈ D.B) (hlk : D.abar l k ≠ 0)
    (hB : D'.B = insert k (D.B.erase l)) (v : Fin m → ℝ) :
    ∑ i ∈ D'.B, extCost c i * rr D' v i =
      ∑ i ∈ D.B, extCost c i * rr D v i + D.cbar c k / D.abar l k * rr D v l := by
  have hx := rr_exchange D D' k l hk hl hlk hB v
  rw [Finset.sum_congr rfl (fun i hi => by rw [hx i hi])]
  have hknot : k ∉ D.B.erase l := fun h => hk (Finset.mem_of_mem_erase h)
  rw [hB, Finset.sum_insert hknot, if_pos rfl]
  rw [Finset.sum_congr rfl (fun i hi => by
    rw [if_neg (fun h : i = k => hknot (h ▸ hi))])]
  unfold Dictionary.cbar
  rw [← Finset.add_sum_erase D.B (fun i => extCost c i * rr D v i) hl,
    ← Finset.add_sum_erase D.B (fun i => extCost c i * D.abar i k) hl]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  have e : ∑ i ∈ D.B.erase l, extCost c i * (D.abar i k * (rr D v l / D.abar l k)) =
      (∑ i ∈ D.B.erase l, extCost c i * D.abar i k) * (rr D v l / D.abar l k) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e]
  field_simp
  ring

end P2M9d2868df

theorem solution
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (D₀ D D' : VanderbeiLP.Simplex.Dictionary A) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (k l : Fin (n + m))
    (henter : D.IsEnteringCandidate c k)
    (hleave : VanderbeiLP.Simplex.Dictionary.IsLexLeaving D₀ D b k l)
    (hB : D'.B = insert k (D.B.erase l)) :
    (∑ i ∈ D'.B, VanderbeiLP.Simplex.extCost c i •
      VanderbeiLP.Simplex.Dictionary.lexRow D₀ D' b i) =
    (∑ i ∈ D.B, VanderbeiLP.Simplex.extCost c i •
      VanderbeiLP.Simplex.Dictionary.lexRow D₀ D b i) +
      (D.cbar c k / D.abar l k) • VanderbeiLP.Simplex.Dictionary.lexRow D₀ D b l := by
  obtain ⟨hk, -⟩ := henter
  obtain ⟨hl, hlk, -⟩ := hleave
  have hrow : ∀ (E : VanderbeiLP.Simplex.Dictionary A) (i : Fin (n + m)) (q : Fin (m + 1)),
      VanderbeiLP.Simplex.Dictionary.lexRow D₀ E b i q =
        P2M9d2868df.rr E ((Fin.cons b (fun p => VanderbeiLP.Simplex.augCol A (D₀.epsVar p)) :
          Fin (m + 1) → (Fin m → ℝ)) q) i := by
    intro E i q
    refine Fin.cases ?_ ?_ q
    · simp [VanderbeiLP.Simplex.Dictionary.lexRow, P2M9d2868df.bbar_eq]
    · intro p
      simp [VanderbeiLP.Simplex.Dictionary.lexRow, P2M9d2868df.abar_eq]
  funext q
  simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hrow]
  exact P2M9d2868df.scalar_identity D D' c k l hk hl hlk.ne' hB _
