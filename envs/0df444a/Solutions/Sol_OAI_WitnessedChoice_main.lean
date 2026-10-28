-- Prove2me | solution 1 for OAI.WitnessedChoice.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T00:23:03.061579+00:00
-- url     : https://prove2.me/submissions/ab6a5eab-ac30-41d6-b5f9-1ff41d376828

import Mathlib
import Definitions.Def_WitnessedChoice
import Definitions.Def_OAIQ4Wc000
import Theorems.Thm_OAI_WitnessedSeparation_Grid_QuotedGrid_formula_value

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_Hereditary
attribute [-instance] _root_.OAI.WitnessedSeparation.Forms.instFintypeElemHFLabelValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w

namespace WitnessedSeparation.Hereditary

noncomputable section

variable {A : Type u} {B : Type v}

attribute [local instance] instDecidableEqHF

theorem mem_wellFounded : WellFounded (fun x y : HF A => x ∈ y) :=
  (measure rank).wf.mono (fun _ _ h => rank_lt_of_mem h)

end



end WitnessedSeparation.Hereditary

end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_SupportGrid
attribute [-instance] _root_.OAI.WitnessedSeparation.Grid.instDecidableRelVertexEdgeIncident _root_.OAI.WitnessedSeparation.Grid.instFiniteConfiguration _root_.OAI.WitnessedSeparation.Grid.instFintypeAtom _root_.OAI.WitnessedSeparation.Grid.instFintypeConfiguration _root_.OAI.WitnessedSeparation.Grid.instFintypeLocalGroup _root_.OAI.WitnessedSeparation.Grid.instMulActionBoxGroupAtom _root_.OAI.WitnessedSeparation.Grid.instMulActionBoxGroupConfiguration _root_.OAI.WitnessedSeparation.Grid.instMulActionCentralGroupAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WitnessedSeparation

namespace Support

theorem omega_swap (u v : Plane) : omega v u = -omega u v := by
  simp [omega]; ring

variable {F K : Type} [Fintype F] [AddCommGroup K] [Module Scalar K]

theorem correction_swap (cycle : F → K) (a b : F → Plane) :
    correction cycle b a = -correction cycle a b := by
  unfold correction
  rw [← smul_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro f _
  rw [omega_swap, neg_smul]

namespace H

variable (cycle : F → K)

theorem commutator (x y : H cycle) :
    x * y * x⁻¹ * y⁻¹ = central cycle (∑ f, omega (x.face f) (y.face f) • cycle f) := by
  apply H.ext
  · simp only [mul_face, inv_face, central]
    abel
  · simp only [mul_flow, mul_face, inv_flow, inv_face,
      correction_add_left, correction_neg_left,
      correction_neg_right, correction_self,
      zero_add, add_zero, central]
    have hc : correction cycle x.face y.face + correction cycle x.face y.face =
        ∑ f, omega (x.face f) (y.face f) • cycle f := by
      rw [correction, ← add_smul]
      have h : (2 : Scalar) + 2 = 1 := by decide
      rw [h, one_smul]
    have hs := correction_swap cycle x.face y.face
    rw [hs]
    abel_nf at hc ⊢
    exact hc

theorem commutator_mem_centralPart (S : Subgroup (H cycle))
    {a b : F → Plane} (ha : a ∈ projected cycle S) (hb : b ∈ projected cycle S) :
    (∑ f, omega (a f) (b f) • cycle f) ∈ centralPart cycle S := by
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨y, hy, rfl⟩ := hb
  rw [mem_centralPart, ← commutator]
  exact S.mul_mem (S.mul_mem (S.mul_mem hx hy) (S.inv_mem hx)) (S.inv_mem hy)

theorem stabilizer_isotropic (S : Subgroup (H cycle)) (lambda : K →ₗ[Scalar] Scalar)
    (hlambda : ∀ k ∈ centralPart cycle S, lambda k = 0)
    {a b : F → Plane} (ha : a ∈ projected cycle S) (hb : b ∈ projected cycle S) :
    (∑ f, lambda (cycle f) * omega (a f) (b f)) = 0 := by
  have h := hlambda _ (commutator_mem_centralPart cycle S ha hb)
  simpa only [map_sum, map_smul, smul_eq_mul, mul_comm] using h

theorem subgroup_card [FiniteDimensional Scalar K] (S : Subgroup (H cycle)) :
    Nat.card S = 3 ^ (Module.finrank Scalar (projected cycle S) +
      Module.finrank Scalar (centralPart cycle S)) := by
  rw [Nat.card_congr (subgroupEquiv cycle S), Nat.card_prod,
    Module.natCard_eq_pow_finrank (K := Scalar) (V := projected cycle S),
    Module.natCard_eq_pow_finrank (K := Scalar) (V := centralPart cycle S)]
  have h : Nat.card Scalar = 3 := by simp [Scalar, Nat.card_eq_fintype_card]
  rw [h, ← pow_add]

theorem ambient_card [FiniteDimensional Scalar K] :
    Nat.card (H cycle) = 3 ^ (Module.finrank Scalar (F → Plane) + Module.finrank Scalar K) := by
  rw [Nat.card_congr (productEquiv cycle), Nat.card_prod,
    Module.natCard_eq_pow_finrank (K := Scalar) (V := F → Plane),
    Module.natCard_eq_pow_finrank (K := Scalar) (V := K)]
  have h : Nat.card Scalar = 3 := by simp [Scalar, Nat.card_eq_fintype_card]
  rw [h, ← pow_add]

theorem subgroup_index [FiniteDimensional Scalar K] (S : Subgroup (H cycle)) :
    S.index = 3 ^ ((Module.finrank Scalar (F → Plane) - Module.finrank Scalar (projected cycle S)) +
      (Module.finrank Scalar K - Module.finrank Scalar (centralPart cycle S))) := by
  have hu := Submodule.finrank_le (projected cycle S)
  have hk := Submodule.finrank_le (centralPart cycle S)
  have hc := S.index_mul_card
  rw [subgroup_card cycle S, ambient_card cycle] at hc
  apply Nat.mul_right_cancel (m := 3 ^ (Module.finrank Scalar (projected cycle S) +
    Module.finrank Scalar (centralPart cycle S))) (by positivity)
  rw [hc, ← pow_add]
  congr 1
  omega

end H

theorem diagonalForm_finrank_ker (weight : F → Scalar) :
    Module.finrank Scalar (diagonalForm weight).ker =
      2 * Fintype.card {f : F // weight f = 0} := by
  classical
  rw [(diagonalKerEquiv weight).finrank_eq, Module.finrank_pi_fintype]
  simp [Plane, Module.finrank_prod, Nat.mul_comm]

theorem nonzero_blocks_le_codim (weight : F → Scalar)
    (U : Submodule Scalar (F → Plane))
    (hisotropic : ∀ a ∈ U, ∀ b ∈ U, diagonalForm weight a b = 0) :
    Fintype.card {f : F // weight f ≠ 0} ≤
      Module.finrank Scalar (F → Plane) - Module.finrank Scalar U := by
  classical
  have hle : U ≤ (diagonalForm weight).orthogonal U := by
    intro a ha
    exact fun b hb => hisotropic b hb a ha
  have hd := Submodule.finrank_mono hle
  have heq := LinearMap.BilinForm.finrank_add_finrank_orthogonal'
    (B := diagonalForm weight) U
  have hker := Submodule.finrank_mono
    (show U ⊓ (diagonalForm weight).ker ≤ (diagonalForm weight).ker from inf_le_right)
  have hcard : Fintype.card {f : F // weight f ≠ 0} =
      Fintype.card F - Fintype.card {f : F // weight f = 0} :=
    Fintype.card_subtype_compl (fun f : F => weight f = 0)
  have hcardle := Fintype.card_subtype_le (fun f : F => weight f = 0)
  have hdimu : Module.finrank Scalar U ≤ Module.finrank Scalar (F → Plane) :=
    Submodule.finrank_le U
  have hdim : Module.finrank Scalar (F → Plane) = 2 * Fintype.card F := by
    rw [Module.finrank_pi_fintype]
    simp [Plane, Module.finrank_prod, Nat.mul_comm]
  rw [diagonalForm_finrank_ker] at hker
  rw [hdim] at heq hdimu ⊢
  omega

end Support

end WitnessedSeparation

namespace WitnessedSeparation.Grid

variable {n : ℕ}

theorem single_mul_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (z : Scalar) (l : ι → Scalar) :
    (∑ j, (Pi.single i z : ι → Scalar) j * l j) = z * l i := by
  classical
  simp only [Pi.single_apply, ite_mul, zero_mul]
  simp

@[simp] theorem curl_xy (l : Edge n → Scalar) (i j : Fin n) (k : Fin (n+1)) :
    curl l (.inl (i,j,k)) = l (ex i j.castSucc k) + l (ey i.succ j k) -
      l (ex i j.succ k) - l (ey i.castSucc j k) := by
  classical
  simp only [curl, cycle, Pi.sub_apply, Pi.add_apply, sub_mul, add_mul,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, single_mul_sum, one_mul]

@[simp] theorem curl_xz (l : Edge n → Scalar) (i k : Fin n) (j : Fin (n+1)) :
    curl l (.inr (.inl (i,j,k))) = l (ex i j k.castSucc) + l (ez i.succ j k) -
      l (ex i j k.succ) - l (ez i.castSucc j k) := by
  classical
  simp only [curl, cycle, Pi.sub_apply, Pi.add_apply, sub_mul, add_mul,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, single_mul_sum, one_mul]

@[simp] theorem curl_yz (l : Edge n → Scalar) (j k : Fin n) (i : Fin (n+1)) :
    curl l (.inr (.inr (i,j,k))) = l (ey i j k.castSucc) + l (ez i j.succ k) -
      l (ey i j k.succ) - l (ez i j.castSucc k) := by
  classical
  simp only [curl, cycle, Pi.sub_apply, Pi.add_apply, sub_mul, add_mul,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, single_mul_sum, one_mul]

@[simp] theorem curl_gradient (φ : Vertex n → Scalar) (f : Face n) :
    curl (gradient φ) f = 0 := by
  rcases f with ⟨i,j,k⟩ | (⟨i,j,k⟩ | ⟨i,j,k⟩)
  all_goals simp [gradient, head, tail, ex, ey, ez]

theorem prefix_step (l : Fin n → Scalar) (i : Fin n) :
    prefixSum l i.succ - prefixSum l i.castSucc = l i := by
  classical
  have h : prefixSum l i.succ = prefixSum l i.castSucc + l i := by
    unfold prefixSum
    have hs : (∑ a : Fin n, if a = i then l a else 0) = l i := by simp
    rw [← hs, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    simp only [Fin.val_succ, Fin.val_castSucc]
    by_cases hai : a.val < i.val
    · have hne : a ≠ i := by intro h; subst a; omega
      simp [hai, hne, show a.val < i.val+1 by omega]
    · by_cases heq : a = i
      · subst a; simp
      · have hge : i.val + 1 ≤ a.val := by
          have : a.val ≠ i.val := by intro h; exact heq (Fin.ext h)
          omega
        simp [hai, heq, show ¬a.val < i.val+1 by omega]
  rw [h]
  abel

@[simp] theorem residual1_x (l : Edge n → Scalar) (i : Fin n) (j k : Fin (n+1)) :
    residual1 l (ex i j k) = 0 := by
  simp only [residual1, Pi.sub_apply, gradient, head, tail, ex, phi1, prefix_step, sub_self]

@[simp] theorem residual2_x (l : Edge n → Scalar) (i0 : Fin (n+1))
    (i : Fin n) (j k : Fin (n+1)) : residual2 l i0 (ex i j k) = 0 := by
  rw [residual2, Pi.sub_apply, residual1_x]
  simp only [gradient, phi2, head, tail, ex, sub_self]

@[simp] theorem residual2_y (l : Edge n → Scalar) (i0 : Fin (n+1))
    (j : Fin n) (k : Fin (n+1)) : residual2 l i0 (ey i0 j k) = 0 := by
  simp only [residual2, Pi.sub_apply, gradient, phi2, head, tail, ey,
    prefix_step, sub_self]

@[simp] theorem residual_x (l : Edge n → Scalar) (i0 : Fin (n+1))
    (i : Fin n) (j k : Fin (n+1)) : residual l i0 (ex i j k) = 0 := by
  rw [residual, Pi.sub_apply, residual2_x]
  simp only [gradient, phi3, head, tail, ex, sub_self]

@[simp] theorem residual_y (l : Edge n → Scalar) (i0 : Fin (n+1))
    (j : Fin n) (k : Fin (n+1)) : residual l i0 (ey i0 j k) = 0 := by
  rw [residual, Pi.sub_apply, residual2_y]
  simp only [gradient, phi3, head, tail, ey, sub_self]

@[simp] theorem residual_z (l : Edge n → Scalar) (i0 : Fin (n+1))
    (k : Fin n) : residual l i0 (ez i0 0 k) = 0 := by
  simp only [residual, Pi.sub_apply, gradient, phi3, head, tail, ez,
    prefix_step, sub_self]

@[simp] theorem curl_residual (l : Edge n → Scalar) (i0 : Fin (n+1)) (f : Face n) :
    curl (residual l i0) f = curl l f := by
  simp [residual, residual2, residual1]

theorem residual_as_gradient (l : Edge n → Scalar) (i0 : Fin (n+1)) :
    residual l i0 = l - gradient (phi1 l + phi2 l i0 + phi3 l i0) := by
  funext e
  simp only [residual, residual2, residual1, Pi.sub_apply, gradient, Pi.add_apply]
  ring

theorem line_constant {g : Fin (n+1) → Scalar}
    (h : ∀ a : Fin n, g a.succ = g a.castSucc) (i j : Fin (n+1)) : g i = g j := by
  have hz : ∀ a, g a = g 0 := by
    intro a
    induction a using Fin.induction with
    | zero => rfl
    | succ a ha => exact (h a).trans ha
  exact (hz i).trans (hz j).symm

theorem residual_y_witness (l : Edge n → Scalar) (i0 i : Fin (n+1))
    (j : Fin n) (k : Fin (n+1)) (h : residual l i0 (ey i j k) ≠ 0) :
    ∃ a : Fin n, curl l (.inl (a,j,k)) ≠ 0 := by
  by_contra hn
  push Not at hn
  have hd : ∀ a : Fin n, residual l i0 (ey a.succ j k) =
      residual l i0 (ey a.castSucc j k) := by
    intro a
    have hc := curl_residual l i0 (.inl (a,j,k))
    rw [curl_xy, residual_x, residual_x, hn a] at hc
    simpa using sub_eq_zero.mp hc
  have hc := line_constant (g := fun a => residual l i0 (ey a j k)) hd i i0
  exact h (hc.trans (residual_y l i0 j k))

theorem residual_z_witness (l : Edge n → Scalar) (i0 i j : Fin (n+1))
    (k : Fin n) (h : residual l i0 (ez i j k) ≠ 0) :
    (∃ a : Fin n, curl l (.inr (.inl (a,j,k))) ≠ 0) ∨
    (∃ b : Fin n, curl l (.inr (.inr (i0,b,k))) ≠ 0) := by
  by_contra hn
  push Not at hn
  have hx : ∀ a : Fin n, residual l i0 (ez a.succ j k) =
      residual l i0 (ez a.castSucc j k) := by
    intro a
    have hc := curl_residual l i0 (.inr (.inl (a,j,k)))
    rw [curl_xz, residual_x, residual_x, hn.1 a] at hc
    simpa using sub_eq_zero.mp hc
  have hy : ∀ b : Fin n, residual l i0 (ez i0 b.succ k) =
      residual l i0 (ez i0 b.castSucc k) := by
    intro b
    have hc := curl_residual l i0 (.inr (.inr (i0,b,k)))
    rw [curl_yz, residual_y, residual_y, hn.2 b] at hc
    simpa using sub_eq_zero.mp hc
  exact h ((line_constant (g := fun a => residual l i0 (ez a j k)) hx i i0).trans ((line_constant (g := fun b => residual l i0 (ez i0 b k)) hy j 0).trans
    (residual_z l i0 k)))

theorem card_le_product_of_witness {α β γ : Type*} [DecidableEq α] [Fintype β]
    (s : Finset α) (t : Finset γ) (f : β → γ → α)
    (h : ∀ x ∈ s, ∃ b c, c ∈ t ∧ f b c = x) :
    s.card ≤ Fintype.card β * t.card := by
  classical
  have hs : s ⊆ (Finset.univ ×ˢ t).image (fun p => f p.1 p.2) := by
    intro x hx
    obtain ⟨b,c,hc,hbc⟩ := h x hx
    exact Finset.mem_image.mpr ⟨(b,c), by simp [hc], hbc⟩
  calc
    s.card ≤ ((Finset.univ ×ˢ t).image (fun p => f p.1 p.2)).card := Finset.card_le_card hs
    _ ≤ (Finset.univ ×ˢ t).card := Finset.card_image_le
    _ = Fintype.card β * t.card := by simp

theorem card_le_two_products_of_witness {α β γ δ ε : Type*} [DecidableEq α]
    [Fintype β] [Fintype δ] (s : Finset α) (t : Finset γ) (u : Finset ε)
    (f : β → γ → α) (g : δ → ε → α)
    (h : ∀ x ∈ s, (∃ b c, c ∈ t ∧ f b c = x) ∨ (∃ d e, e ∈ u ∧ g d e = x)) :
    s.card ≤ Fintype.card β * t.card + Fintype.card δ * u.card := by
  classical
  let sf := (Finset.univ ×ˢ t).image (fun p => f p.1 p.2)
  let sg := (Finset.univ ×ˢ u).image (fun p => g p.1 p.2)
  have hs : s ⊆ sf ∪ sg := by
    intro x hx
    rcases h x hx with ⟨b,c,hc,hbc⟩ | ⟨d,e,he,hde⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(b,c), by simp [hc], hbc⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(d,e), by simp [he], hde⟩)
  calc
    s.card ≤ (sf ∪ sg).card := Finset.card_le_card hs
    _ ≤ sf.card + sg.card := Finset.card_union_le _ _
    _ ≤ (Finset.univ ×ˢ t).card + (Finset.univ ×ˢ u).card :=
      Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ = _ := by simp

theorem sum_badSlice (l : Edge n → Scalar) :
    (∑ i : Fin (n+1), (badSlice l i).card) = (badYZ l).card := by
  simp only [badSlice, badYZ, nonzeroSet, Finset.card_filter, Fintype.sum_prod_type]

theorem exists_sparse_slice (l : Edge n → Scalar) :
    ∃ i0 : Fin (n+1), (n+1) * (badSlice l i0).card ≤ (badYZ l).card := by
  obtain ⟨i0, _, hi⟩ := Finset.exists_min_image Finset.univ
    (fun i : Fin (n+1) => (badSlice l i).card) (by simp)
  refine ⟨i0, ?_⟩
  calc
    (n+1) * (badSlice l i0).card = ∑ _ : Fin (n+1), (badSlice l i0).card := by simp
    _ ≤ ∑ i : Fin (n+1), (badSlice l i).card := Finset.sum_le_sum hi
    _ = _ := sum_badSlice l

theorem count_residual_y (l : Edge n → Scalar) (i0 : Fin (n+1)) :
    (nonzeroSet (fun p : EdgeY n => residual l i0 (ey p.1 p.2.1 p.2.2))).card ≤
      (n+1) * (badXY l).card := by
  have h := card_le_product_of_witness (β := Fin (n+1))
    (nonzeroSet (fun p : EdgeY n => residual l i0 (ey p.1 p.2.1 p.2.2)))
    (badXY l) (fun i f => (i,f.2.1,f.2.2)) (by
      rintro ⟨i,j,k⟩ hx
      obtain ⟨a,ha⟩ := residual_y_witness l i0 i j k (by simpa only [mem_nonzeroSet] using hx)
      exact ⟨i,(a,j,k), by simpa [badXY] using ha, rfl⟩)
  simpa only [Fintype.card_fin] using h

theorem count_residual_z (l : Edge n → Scalar) (i0 : Fin (n+1)) :
    (nonzeroSet (fun p : EdgeZ n => residual l i0 (ez p.1 p.2.1 p.2.2))).card ≤
      (n+1) * (badXZ l).card + (n+1)^2 * (badSlice l i0).card := by
  have h := card_le_two_products_of_witness (β := Fin (n+1))
    (δ := Fin (n+1) × Fin (n+1))
    (nonzeroSet (fun p : EdgeZ n => residual l i0 (ez p.1 p.2.1 p.2.2)))
    (badXZ l) (badSlice l i0) (fun i f => (i,f.2.1,f.2.2))
    (fun p f => (p.1,p.2,f.2)) (by
      rintro ⟨i,j,k⟩ hx
      rcases residual_z_witness l i0 i j k (by simpa only [mem_nonzeroSet] using hx) with ⟨a,ha⟩ | ⟨b,hb⟩
      · exact Or.inl ⟨i,(a,j,k), by simpa [badXZ] using ha, rfl⟩
      · exact Or.inr ⟨(i,j),(b,k), by simpa [badSlice] using hb, rfl⟩)
  simpa only [Fintype.card_fin, Fintype.card_prod, pow_two] using h

theorem count_curl (l : Edge n → Scalar) :
    (nonzeroSet (curl l)).card = (badXY l).card + (badXZ l).card + (badYZ l).card := by
  simp only [nonzeroSet, badXY, badXZ, badYZ, Finset.card_filter, Fintype.sum_sum_type]
  omega

theorem count_residual (l : Edge n → Scalar) (i0 : Fin (n+1)) :
    (nonzeroSet (residual l i0)).card ≤
      (n+1) * ((badXY l).card + (badXZ l).card) + (n+1)^2 * (badSlice l i0).card := by
  have heq : (nonzeroSet (residual l i0)).card =
      (nonzeroSet (fun p : EdgeY n => residual l i0 (ey p.1 p.2.1 p.2.2))).card +
      (nonzeroSet (fun p : EdgeZ n => residual l i0 (ez p.1 p.2.1 p.2.2))).card := by
    simp only [nonzeroSet, Finset.card_filter, Fintype.sum_sum_type]
    have hx : (∑ p : EdgeX n, if residual l i0 (.inl p) ≠ 0 then 1 else 0) = (0 : ℕ) := by
      apply Finset.sum_eq_zero
      rintro ⟨i,j,k⟩ _
      change (if residual l i0 (ex i j k) ≠ 0 then 1 else 0) = 0
      simp only [residual_x, ne_eq, not_true_eq_false, ite_false]
    rw [hx, zero_add]
    rfl
  rw [heq, Nat.mul_add]
  have hy := count_residual_y l i0
  have hz := count_residual_z l i0
  omega

theorem sparse_cochain (l : Edge n → Scalar) :
    ∃ φ : Vertex n → Scalar,
      (nonzeroSet (l - gradient φ)).card ≤ (n+1) * (nonzeroSet (curl l)).card := by
  obtain ⟨i0,hi⟩ := exists_sparse_slice l
  refine ⟨phi1 l + phi2 l i0 + phi3 l i0, ?_⟩
  rw [← residual_as_gradient, count_curl]
  calc
    (nonzeroSet (residual l i0)).card ≤
      (n+1) * ((badXY l).card + (badXZ l).card) + (n+1)^2 * (badSlice l i0).card :=
        count_residual l i0
    _ ≤ (n+1) * ((badXY l).card + (badXZ l).card) + (n+1) * (badYZ l).card := by
      apply Nat.add_le_add_left
      simpa only [pow_two, Nat.mul_assoc] using Nat.mul_le_mul_left (n+1) hi
    _ = _ := by ring

end WitnessedSeparation.Grid

end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_GridAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WitnessedSeparation.Grid

noncomputable section

open Support

variable {n : ℕ}

theorem pairing_boundary (φ : Vertex n → Scalar) (z : Edge n → Scalar) :
    pairing φ (boundary z) = pairing (gradient φ) z := by
  have hb : boundary z = ∑ e : Edge n, z e •
      ((Pi.single (head e) (1 : Scalar) : Vertex n → Scalar) - Pi.single (tail e) 1) := rfl
  rw [hb]
  simp only [map_sum, map_smul, map_sub, pairing_single, mul_one, smul_eq_mul]
  change (∑ e, z e * (φ (head e) - φ (tail e))) =
    ∑ e, (φ (head e) - φ (tail e)) * z e
  apply Finset.sum_congr rfl
  intro e _
  ring

@[simp] theorem pairing_gradient_flow (φ : Vertex n → Scalar) (k : FlowSpace n) :
    pairing (gradient φ) k.val = 0 := by
  rw [← pairing_boundary, LinearMap.mem_ker.mp k.property, map_zero]

theorem pairing_sub {ι : Type*} [Fintype ι] (l r z : ι → Scalar) :
    pairing (l-r) z = pairing l z - pairing r z := by
  simp only [pairing, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply,
    sub_mul, Finset.sum_sub_distrib]

theorem exists_representative (lambda : FlowSpace n →ₗ[Scalar] Scalar) :
    ∃ l : Edge n → Scalar, ∀ k : FlowSpace n, pairing l k.val = lambda k := by
  obtain ⟨g,hg⟩ := LinearMap.exists_extend lambda
  let l : Edge n → Scalar := fun e => g (Pi.single e 1)
  have hrep (z : Edge n → Scalar) : g z = pairing l z := by
    have hz : (∑ e : Edge n, z e • Pi.single e (1 : Scalar)) = z := by
      classical
      ext e
      simp [Finset.sum_apply, Pi.single_apply]
    calc
      g z = g (∑ e : Edge n, z e • Pi.single e (1 : Scalar)) := congrArg g hz.symm
      _ = ∑ e, z e * l e := by simp only [map_sum, map_smul, smul_eq_mul]; rfl
      _ = pairing l z := by
        change (∑ e, z e * l e) = ∑ e, l e * z e
        apply Finset.sum_congr rfl
        intro e _
        ring
  refine ⟨l, fun k => ?_⟩
  rw [← hrep]
  exact LinearMap.congr_fun hg k

theorem curl_representative (lambda : FlowSpace n →ₗ[Scalar] Scalar) (l : Edge n → Scalar)
    (hl : ∀ k : FlowSpace n, pairing l k.val = lambda k) (f : Face n) :
    curl l f = lambda (flowCycle f) := by
  rw [← hl]
  simp only [curl, pairing, LinearMap.coe_mk, AddHom.coe_mk, flowCycle, mul_comm]

theorem curl_count_le_codim (S : Subgroup (BoxGroup n))
    (lambda : FlowSpace n →ₗ[Scalar] Scalar)
    (hlambda : lambda ∈ (Support.H.centralPart flowCycle S).dualAnnihilator)
    (l : Edge n → Scalar) (hl : ∀ k : FlowSpace n, pairing l k.val = lambda k) :
    (nonzeroSet (curl l)).card ≤ faceCodim S := by
  classical
  have hiso : ∀ a ∈ Support.H.projected flowCycle S,
      ∀ b ∈ Support.H.projected flowCycle S, Support.diagonalForm (curl l) a b = 0 := by
    intro a ha b hb
    simp only [Support.diagonalForm_apply, curl_representative lambda l hl]
    exact Support.H.stabilizer_isotropic flowCycle S lambda
      ((Submodule.mem_dualAnnihilator lambda).mp hlambda) ha hb
  have h := Support.nonzero_blocks_le_codim (curl l)
    (Support.H.projected flowCycle S) hiso
  simpa only [nonzeroSet, faceCodim, Fintype.card_subtype] using h

theorem sparse_annihilator (S : Subgroup (BoxGroup n))
    (lambda : FlowSpace n →ₗ[Scalar] Scalar)
    (hlambda : lambda ∈ (Support.H.centralPart flowCycle S).dualAnnihilator) :
    ∃ r : Edge n → Scalar,
      (∀ k : FlowSpace n, pairing r k.val = lambda k) ∧
      (nonzeroSet r).card ≤ (n+1) * faceCodim S := by
  obtain ⟨l,hl⟩ := exists_representative lambda
  obtain ⟨φ,hφ⟩ := sparse_cochain l
  refine ⟨l - gradient φ, ?_, hφ.trans (Nat.mul_le_mul_left _ (curl_count_le_codim S lambda hlambda l hl))⟩
  intro k
  rw [pairing_sub, pairing_gradient_flow, sub_zero, hl]

theorem subgroup_support_edges (S : Subgroup (BoxGroup n)) :
    ∃ T : Finset (Edge n),
      T.card ≤ (n+1) * faceCodim S * flowCodim S ∧
      ∀ k : FlowSpace n, (∀ e ∈ T, k.val e = 0) →
        Support.H.central flowCycle k ∈ S := by
  classical
  let W := (Support.H.centralPart flowCycle S).dualAnnihilator
  let : Module.Free Scalar W := Module.Free.of_divisionRing Scalar W
  let b := Module.finBasis Scalar W
  have hd : Module.finrank Scalar W = flowCodim S := by
    have h := Subspace.finrank_add_finrank_dualAnnihilator_eq
      (Support.H.centralPart flowCycle S)
    change Module.finrank Scalar (Support.H.centralPart flowCycle S) +
      Module.finrank Scalar W = Module.finrank Scalar (FlowSpace n) at h
    unfold flowCodim
    omega
  have hr : ∀ i : Fin (Module.finrank Scalar W), ∃ r : Edge n → Scalar,
      (∀ k : FlowSpace n, pairing r k.val = (b i).val k) ∧
      (nonzeroSet r).card ≤ (n+1) * faceCodim S := by
    intro i
    exact sparse_annihilator S (b i).val (b i).property
  choose r hr hbnd using hr
  let T := Finset.univ.biUnion (fun i => nonzeroSet (r i))
  refine ⟨T, ?_, ?_⟩
  · calc
      T.card ≤ ∑ i : Fin (Module.finrank Scalar W), (nonzeroSet (r i)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _ : Fin (Module.finrank Scalar W), (n+1) * faceCodim S :=
        Finset.sum_le_sum (fun i _ => hbnd i)
      _ = (n+1) * faceCodim S * flowCodim S := by simp [hd, Nat.mul_comm]
  · intro k hk
    apply (Support.H.mem_centralPart flowCycle S k).mp
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff
      (Support.H.centralPart flowCycle S) k).mp
    have hbi (i : Fin (Module.finrank Scalar W)) : (b i).val k = 0 := by
      rw [← hr i k]
      change (∑ e, r i e * k.val e) = 0
      apply Finset.sum_eq_zero
      intro e _
      by_cases he : r i e = 0
      · simp [he]
      · have hmem : e ∈ T := Finset.mem_biUnion.mpr
          ⟨i, Finset.mem_univ _, (mem_nonzeroSet _ _).mpr he⟩
        simp [hk e hmem]
    intro lambda hlambda
    let w : W := ⟨lambda, hlambda⟩
    have heq := congrArg (fun w : W => w.val k) (b.sum_repr w)
    simp only [Submodule.coe_sum, Submodule.coe_smul, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, hbi, mul_zero, Finset.sum_const_zero] at heq
    exact heq.symm

theorem box_subgroup_index (S : Subgroup (BoxGroup n)) :
    S.index = 3 ^ (faceCodim S + flowCodim S) :=
  Support.H.subgroup_index flowCycle S

theorem orbit_card_eq_power {X : Type*} [MulAction (BoxGroup n) X] (x : X) :
    Nat.card (MulAction.orbit (BoxGroup n) x) =
      3 ^ (faceCodim (MulAction.stabilizer (BoxGroup n) x) +
        flowCodim (MulAction.stabilizer (BoxGroup n) x)) := by
  rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (BoxGroup n) x)]
  exact box_subgroup_index (MulAction.stabilizer (BoxGroup n) x)

theorem small_orbit_support_edges {X : Type*} [MulAction (BoxGroup n) X]
    (x : X) (N : ℕ) (hN : 0 < N) (q : ℝ) (_hq : 0 ≤ q)
    (horbit : (Nat.card (MulAction.orbit (BoxGroup n) x) : ℝ) ≤ (N : ℝ) ^ q) :
    ∃ T : Finset (Edge n),
      (T.card : ℝ) ≤ 2 * (n+1 : ℝ) * (q * Real.logb 3 N)^2 ∧
      ∀ k : FlowSpace n, (∀ e ∈ T, k.val e = 0) →
        Support.H.central flowCycle k • x = x := by
  let S := MulAction.stabilizer (BoxGroup n) x
  obtain ⟨T,hcard,hfix⟩ := subgroup_support_edges S
  have heq := orbit_card_eq_power (n := n) x
  have horbit' : (3 : ℝ) ^ (faceCodim S + flowCodim S) ≤ (N : ℝ) ^ q := by
    rw [heq, Nat.cast_pow, Nat.cast_ofNat] at horbit
    exact horbit
  have hlog := Real.logb_le_logb_of_le (b := 3) (by norm_num : (1 : ℝ) < 3)
    (by positivity : (0 : ℝ) < 3 ^ (faceCodim S + flowCodim S)) horbit'
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one,
    Real.logb_rpow_eq_mul_logb_of_pos (by exact_mod_cast hN), Nat.cast_add] at hlog
  have ha : 0 ≤ (faceCodim S : ℝ) := Nat.cast_nonneg _
  have hd : 0 ≤ (flowCodim S : ℝ) := Nat.cast_nonneg _
  have hab : (faceCodim S : ℝ) * flowCodim S ≤ (q * Real.logb 3 N)^2 := by
    nlinarith [sq_nonneg ((faceCodim S : ℝ) - flowCodim S)]
  have hc : (T.card : ℝ) ≤ (n+1 : ℝ) * faceCodim S * flowCodim S := by
    exact_mod_cast hcard
  refine ⟨T, ?_, fun k hk => hfix k hk⟩
  calc
    (T.card : ℝ) ≤ (n+1 : ℝ) * faceCodim S * flowCodim S := hc
    _ ≤ (n+1 : ℝ) * (q * Real.logb 3 N)^2 := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hab (by positivity)
    _ ≤ 2 * (n+1 : ℝ) * (q * Real.logb 3 N)^2 := by
      have hpos : 0 ≤ (n+1 : ℝ) * (q * Real.logb 3 N)^2 := by positivity
      nlinarith

end



open Support

end WitnessedSeparation.Grid

namespace WitnessedSeparation.Grid

variable {n : ℕ}

theorem head_injective_on_axis {e e' : Edge n}
    (ha : edgeAxis e = edgeAxis e') (hh : head e = head e') : e = e' := by
  rcases e with ⟨i,j,k⟩ | (⟨i,j,k⟩ | ⟨i,j,k⟩)
  all_goals rcases e' with ⟨i',j',k'⟩ | (⟨i',j',k'⟩ | ⟨i',j',k'⟩)
  all_goals simp_all [edgeAxis,head]

theorem tail_injective_on_axis {e e' : Edge n}
    (ha : edgeAxis e = edgeAxis e') (hh : tail e = tail e') : e = e' := by
  rcases e with ⟨i,j,k⟩ | (⟨i,j,k⟩ | ⟨i,j,k⟩)
  all_goals rcases e' with ⟨i',j',k'⟩ | (⟨i',j',k'⟩ | ⟨i',j',k'⟩)
  all_goals simp_all [edgeAxis,tail]

theorem degree_le_six (v : Vertex n) :
    Fintype.card {e : Edge n // head e = v ∨ tail e = v} ≤ 6 := by
  classical
  let f : {e : Edge n // head e = v ∨ tail e = v} → Fin 3 × Bool :=
    fun e => (edgeAxis e.val, decide (head e.val = v))
  have hf : Function.Injective f := by
    intro e e' heq
    have ha : edgeAxis e.val = edgeAxis e'.val := congrArg Prod.fst heq
    have hb : decide (head e.val = v) = decide (head e'.val = v) := congrArg Prod.snd heq
    apply Subtype.ext
    by_cases he : head e.val = v
    · have he' : head e'.val = v := by simpa only [he,decide_true,true_eq_decide_iff] using hb
      exact head_injective_on_axis ha (he.trans he'.symm)
    · have he' : head e'.val ≠ v := by simpa only [he,decide_false,false_eq_decide_iff] using hb
      exact tail_injective_on_axis ha
        ((e.property.resolve_left he).trans (e'.property.resolve_left he').symm)
  have h := Fintype.card_le_of_injective f hf
  simpa using h

end WitnessedSeparation.Grid



namespace WitnessedSeparation.Grid

open Support

variable {n : ℕ} {b : Vertex n → Scalar}

theorem edge_support_tuple {X : Type*} [MulAction (BoxGroup n) X]
    (T : Finset (Edge n)) (x : X)
    (hx : ∀ k : FlowSpace n, (∀ e ∈ T, k.val e = 0) →
      Support.H.central flowCycle k • x = x) :
    ∃ alpha : Fin T.card → Atom b, ∀ k : CentralGroup n,
      (∀ i, k • alpha i = alpha i) → centralHom k • x = x := by
  classical
  let alpha (i : Fin T.card) : Atom b := zeroEdgeAtom b ((T.equivFin).symm i).val
  refine ⟨alpha,?_⟩
  intro k hk
  apply hx k.toAdd
  intro e he
  let i : Fin T.card := T.equivFin ⟨e,he⟩
  have hi : ((T.equivFin).symm i).val = e := by simp [i]
  have hfix := hk i
  change Support.H.central flowCycle k.toAdd •
      zeroEdgeAtom b ((T.equivFin).symm i).val = _ at hfix
  rw [central_fix_zeroEdgeAtom_iff] at hfix
  simpa only [hi] using hfix

end WitnessedSeparation.Grid



end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_Counting
attribute [-instance] _root_.OAI.WitnessedSeparation.Forms.instFintypeElemHFLabelValues _root_.OAI.WitnessedSeparation.Forms.instFintypeMolecules
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace WitnessedSeparation.Grid

noncomputable section

open Classical Support

variable {n : ℕ} {b b' b'' : Vertex n → Scalar}

theorem AtomShift.symm {t : Edge n → Scalar} {x : Atom b} {y : Atom b'}
    (h : AtomShift t x y) : AtomShift (-t) y x := by
  cases h with
  | edge e s => simpa using (AtomShift.edge (b := b') (b' := b) (t := -t) e (shiftLocal e (t e) s))
  | config v s h =>
    have hh : boundary (-t) v = b v - b' v := by simp only [map_neg,Pi.neg_apply,h]; abel
    have he : (s.shift t h).shift (-t) hh = s := by apply Configuration.ext; intro e; simp
    simpa only [he] using (AtomShift.config (t := -t) v (s.shift t h) hh)

theorem AtomShift.functional {t : Edge n → Scalar} {x : Atom b} {y z : Atom b'}
    (hy : AtomShift t x y) (hz : AtomShift t x z) : y = z := by
  cases hy <;> cases hz <;> rfl

theorem AtomShift.equal_iff {t : Edge n → Scalar} {x x' : Atom b} {y y' : Atom b'}
    (h : AtomShift t x y) (h' : AtomShift t x' y') : x = x' ↔ y = y' := by
  constructor
  · intro he; subst x'; exact h.functional h'
  · intro he; subst y'; exact h.symm.functional h'.symm

theorem AtomShift.relation {t : Edge n → Scalar} {r : Symbol}
    {x x' : Atom b} {y y' : Atom b'} (h : AtomShift t x y) (h' : AtomShift t x' y')
    (hr : AtomRelation b r x x') : AtomRelation b' r y y' := by
  cases hr with
  | ed e s => cases h; cases h'; exact .ed _ _
  | cf v s => cases h; cases h'; exact .cf _ _
  | eb e s a => cases h; cases h'; exact .eb _ _ _
  | vb v s a => cases h; cases h'; exact .vb _ _ _
  | inc v s e => cases h; cases h'; exact .inc _ _ e
  | z e s a δ hz =>
    cases h; cases h'
    apply AtomRelation.z
    simpa only [shiftLocal,mul_inv_rev,mul_assoc,inv_mul_cancel_left] using hz

theorem AtomShift.relation_iff {t : Edge n → Scalar} {r : Symbol}
    {x x' : Atom b} {y y' : Atom b'} (h : AtomShift t x y) (h' : AtomShift t x' y') :
    AtomRelation b r x x' ↔ AtomRelation b' r y y' :=
  ⟨fun hr => h.relation h' hr,fun hr => h.symm.relation h'.symm hr⟩

end

end WitnessedSeparation.Grid



namespace WitnessedSeparation.Counting

noncomputable section

variable {R I A B : Type*}

namespace Formula

variable [DecidableEq I]

theorem free_conjoin_subset (l : List (Formula R I)) (S : Finset I)
    (h : ∀ φ ∈ l, φ.free ⊆ S) : (conjoin l).free ⊆ S := by
  induction l with
  | nil => simp [conjoin,free]
  | cons φ l ih =>
    exact Finset.union_subset (h φ (by simp)) (ih (fun ψ hψ => h ψ (by simp [hψ])))

end Formula

variable [DecidableEq I]

theorem type_separator (S : Structure R A) (T : Structure R B) (names : Finset I)
    (v : I → A) (w : I → B) (hne : typeOf S names v ≠ typeOf T names w) :
    ∃ φ : Formula R I, φ.free ⊆ names ∧ φ.eval S v ∧ ¬ φ.eval T w := by
  classical
  have h : ¬ ∀ φ : Formula R I, φ.free ⊆ names → (φ.eval S v ↔ φ.eval T w) :=
    fun heq => hne ((typeOf_eq_iff S T names v w).mpr heq)
  push Not at h
  obtain ⟨φ,hφ,hdiff⟩ := h
  by_cases hv : φ.eval S v
  · exact ⟨φ,hφ,hv,by tauto⟩
  · have hw : φ.eval T w := by tauto
    exact ⟨.neg φ,hφ,hv,fun hn => hn hw⟩

theorem isolate_type [Fintype I] [Fintype A] [Fintype B]
    (S : Structure R A) (T : Structure R B) (names : Finset I) (v₀ : I → A) :
    ∃ θ : Formula R I, θ.free ⊆ names ∧
      (∀ v, θ.eval S v ↔ typeOf S names v = typeOf S names v₀) ∧
      (∀ w, θ.eval T w ↔ typeOf T names w = typeOf S names v₀) := by
  classical
  let Z := (I → A) ⊕ (I → B)
  let ev : Z → Formula R I → Prop := fun z φ => z.elim (φ.eval S) (φ.eval T)
  let tp : Z → Set (Formula R I) := fun z =>
    z.elim (typeOf S names) (typeOf T names)
  have heq (z : Z) (φ : Formula R I) (hφ : φ.free ⊆ names)
      (h : tp z = typeOf S names v₀) : ev z φ ↔ φ.eval S v₀ := by
    cases z with
    | inl v => exact (typeOf_eq_iff S S names v v₀).mp h φ hφ
    | inr w => exact (typeOf_eq_iff T S names w v₀).mp h φ hφ
  have hcut : ∀ z : Z, ∃ φ : Formula R I,
      φ.free ⊆ names ∧ φ.eval S v₀ ∧ (ev z φ → tp z = typeOf S names v₀) := by
    intro z
    by_cases h : tp z = typeOf S names v₀
    · exact ⟨.neg .falsum,Finset.empty_subset _,not_false,fun _ => h⟩
    · have hs : ∃ φ : Formula R I, φ.free ⊆ names ∧ φ.eval S v₀ ∧ ¬ ev z φ := by
        cases z with
        | inl v => exact type_separator S S names v₀ v (Ne.symm h)
        | inr w => exact type_separator S T names v₀ w (Ne.symm h)
      obtain ⟨φ,hφ,hv,hw⟩ := hs
      exact ⟨φ,hφ,hv,fun h' => (hw h').elim⟩
  choose cut hfree htrue hcut using hcut
  let l := (Finset.univ : Finset Z).toList.map cut
  let θ := Formula.conjoin l
  have hf : θ.free ⊆ names := by
    apply Formula.free_conjoin_subset
    intro φ hφ
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hφ
    exact hfree z
  have hall (z : Z) : ev z θ ↔ tp z = typeOf S names v₀ := by
    have hc : ev z θ ↔ ∀ φ ∈ l, ev z φ := by
      cases z with
      | inl v => exact Formula.eval_conjoin S l v
      | inr w => exact Formula.eval_conjoin T l w
    rw [hc]
    constructor
    · intro h
      exact hcut z (h (cut z) (List.mem_map.mpr ⟨z,Finset.mem_toList.mpr (Finset.mem_univ z),rfl⟩))
    · intro h φ hφ
      obtain ⟨z',hz',rfl⟩ := List.mem_map.mp hφ
      exact (heq z (cut z') (hfree z') h).mpr (htrue z')
  exact ⟨θ,hf,fun v => hall (.inl v),fun w => hall (.inr w)⟩

theorem extension_equiv [Fintype I] [Fintype A] [Fintype B]
    (S : Structure R A) (T : Structure R B) (names : Finset I) (i : I)
    (_hi : i ∉ names) (v v₀ : I → A) (w : I → B)
    (htype : typeOf S names v = typeOf T names w) :
    Nonempty ({a : A // typeOf S (insert i names) (Function.update v i a) =
          typeOf S (insert i names) v₀} ≃
        {b : B // typeOf T (insert i names) (Function.update w i b) =
          typeOf S (insert i names) v₀}) := by
  classical
  obtain ⟨θ,hfree,hS,hT⟩ := isolate_type S T (insert i names) v₀
  let X := {a : A // θ.eval S (Function.update v i a)}
  let Y := {b : B // θ.eval T (Function.update w i b)}
  let : Fintype X := Fintype.ofFinite X
  let n := Fintype.card X
  have hf : (Formula.exact i n θ).free ⊆ names := by
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    have hmem := hfree (Finset.mem_erase.mp hj).2
    exact (Finset.mem_insert.mp hmem).resolve_left hji
  have hn : (Formula.exact i n θ).eval S v := ⟨Fintype.equivFin X⟩
  have hn' := (typeOf_eq_iff S T names v w).mp htype (.exact i n θ) hf |>.mp hn
  obtain ⟨e⟩ := hn'
  let eS := Equiv.subtypeEquivRight (fun a => hS (Function.update v i a))
  let eT := Equiv.subtypeEquivRight (fun b => hT (Function.update w i b))
  exact ⟨eS.symm.trans ((Fintype.equivFin X).trans (e.symm.trans eT))⟩

end





noncomputable section

variable {R I A B : Type*} [DecidableEq I]

theorem typeOf_project (S : Structure R A) (T : Structure R B)
    {names small : Finset I} (hsub : small ⊆ names) {v : I → A} {w : I → B}
    (h : typeOf S names v = typeOf T names w) :
    typeOf S small v = typeOf T small w := by
  apply (typeOf_eq_iff _ _ _ _ _).mpr
  intro φ hf
  exact (typeOf_eq_iff _ _ _ _ _).mp h φ (hf.trans hsub)

theorem typeOf_permute (S : Structure R A) (T : Structure R B)
    (names : Finset I) (e : I ≃ I) {v : I → A} {w : I → B}
    (h : typeOf S names v = typeOf T names w) :
    typeOf S (names.map e.symm.toEmbedding) (v ∘ e) =
      typeOf T (names.map e.symm.toEmbedding) (w ∘ e) := by
  apply (typeOf_eq_iff _ _ _ _ _).mpr
  intro φ hf
  have hf' : (φ.rename e).free ⊆ names := by
    rw [Formula.free_rename]
    intro i hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hi
    obtain ⟨k,hk,hkj⟩ := Finset.mem_map.mp (hf hj)
    simpa only [Equiv.toEmbedding_apply,← hkj,Equiv.apply_symm_apply] using hk
  simpa using (typeOf_eq_iff _ _ _ _ _).mp h (φ.rename e) hf'

theorem extension_bijection [Fintype I] [Fintype A] [Fintype B]
    (S : Structure R A) (T : Structure R B) (names : Finset I) (i : I)
    (hi : i ∉ names) (v : I → A) (w : I → B)
    (h : typeOf S names v = typeOf T names w) :
    ∃ e : A ≃ B, ∀ a, typeOf S (insert i names) (Function.update v i a) =
      typeOf T (insert i names) (Function.update w i (e a)) := by
  classical
  let f : A → Set (Formula R I) := fun a =>
    typeOf S (insert i names) (Function.update v i a)
  let g : B → Set (Formula R I) := fun b =>
    typeOf T (insert i names) (Function.update w i b)
  have he : ∀ ρ, Nonempty ({a // f a = ρ} ≃ {b // g b = ρ}) := by
    intro ρ
    by_cases ha : ∃ a, f a = ρ
    · obtain ⟨a,rfl⟩ := ha
      exact extension_equiv S T names i hi v (Function.update v i a) w h
    · by_cases hb : ∃ b, g b = ρ
      · obtain ⟨b,rfl⟩ := hb
        obtain ⟨e⟩ := extension_equiv T S names i hi w (Function.update w i b) v h.symm
        exact False.elim (ha ⟨(e ⟨b,rfl⟩).1,(e ⟨b,rfl⟩).2⟩)
      · let : IsEmpty {a // f a = ρ} := ⟨fun a => ha ⟨a.1,a.2⟩⟩
        let : IsEmpty {b // g b = ρ} := ⟨fun b => hb ⟨b.1,b.2⟩⟩
        exact ⟨Equiv.equivOfIsEmpty _ _⟩
  let e := Equiv.ofFiberEquiv (fun ρ => Classical.choice (he ρ))
  refine ⟨e,fun a => ?_⟩
  change f a = g (e a)
  exact (Equiv.ofFiberEquiv_map (fun ρ => Classical.choice (he ρ)) a).symm

theorem extend_type [Fintype I] [Fintype A] [Fintype B]
    (S : Structure R A) (T : Structure R B) (names extra : Finset I)
    (v : I → A) (w : I → B) (h : typeOf S names v = typeOf T names w) :
    ∃ w' : I → B, typeOf S (names ∪ extra) v = typeOf T (names ∪ extra) w' ∧
      ∀ i ∈ names, w' i = w i := by
  classical
  induction extra using Finset.induction_on with
  | empty => exact ⟨w,by simpa using h,fun _ _ => rfl⟩
  | @insert i extra hi ih =>
    obtain ⟨w',ht,hw⟩ := ih
    by_cases hin : i ∈ names ∪ extra
    · have heq : names ∪ insert i extra = names ∪ extra := by
        rw [Finset.union_insert,Finset.insert_eq_of_mem hin]
      exact ⟨w',heq ▸ ht,hw⟩
    · obtain ⟨e,he⟩ := extension_bijection S T (names ∪ extra) i hin v w' ht
      refine ⟨Function.update w' i (e (v i)),?_,?_⟩
      · have ht' := he (v i)
        have heq : names ∪ insert i extra = insert i (names ∪ extra) := by
          ext j; simp only [Finset.mem_union,Finset.mem_insert]; tauto
        simpa only [heq,Function.update_eq_self] using ht'
      · intro j hj
        have hji : j ≠ i := by
          intro heq
          apply hin
          rw [←heq]
          exact Finset.mem_union_left extra hj
        rw [Function.update_of_ne hji]
        exact hw j hj

section Tuple

variable {J J' : Type*} [Fintype J] [Fintype J']

theorem tupleType_project [Nonempty A] [Nonempty B]
    (S : Structure R A) (T : Structure R B) (e : J ↪ I) (e' : J' ↪ I)
    (u : J' ↪ J) (a : J → A) (b : J → B)
    (h : tupleType S e a = tupleType T e b) :
    tupleType S e' (a ∘ u) = tupleType T e' (b ∘ u) := by
  classical
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair e' (fun j => e (u j))
    e'.injective (e.injective.comp u.injective)
  have hm : (tupleNames (u.trans e)).map σ.symm.toEmbedding = tupleNames e' := by
    ext i
    simp only [Finset.mem_map,Equiv.toEmbedding_apply,mem_tupleNames]
    constructor
    · rintro ⟨k,⟨j,rfl⟩,rfl⟩
      exact ⟨j,by simp only [Function.Embedding.trans_apply,← hσ j,σ.symm_apply_apply]⟩
    · rintro ⟨j,rfl⟩
      refine ⟨e (u j),⟨j,rfl⟩,?_⟩
      rw [← hσ j,σ.symm_apply_apply]
  have hs : tupleNames (u.trans e) ⊆ tupleNames e := by
    intro i hi
    obtain ⟨j,rfl⟩ := (mem_tupleNames _ _).mp hi
    exact (mem_tupleNames _ _).mpr ⟨u j,rfl⟩
  have hp := typeOf_project S T hs h
  have ht := typeOf_permute S T (tupleNames (u.trans e)) σ hp
  rw [hm] at ht
  rw [tupleType_assignment S e' (a ∘ u) (tupleAssignment e a ∘ σ)
    (fun j => by simp [hσ]),
    tupleType_assignment T e' (b ∘ u) (tupleAssignment e b ∘ σ)
    (fun j => by simp [hσ])]
  exact ht

theorem tupleType_extend [Fintype I] [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B]
    (S : Structure R A) (T : Structure R B) (e : J ↪ I) (e' : J' ↪ I)
    (u : J ↪ J') (a : J' → A) (b : J → B)
    (h : tupleType S e (a ∘ u) = tupleType T e b) :
    ∃ b' : J' → B, b' ∘ u = b ∧ tupleType S e' a = tupleType T e' b' := by
  classical
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair e (fun j => e' (u j))
    e.injective (e'.injective.comp u.injective)
  let v := tupleAssignment e' a
  let w := tupleAssignment e b ∘ σ.symm
  have hw (j : J) : w (e' (u j)) = b j := by
    simp [w,Function.comp_def,←hσ j]
  have hn : (tupleNames e).map σ.toEmbedding = tupleNames (u.trans e') := by
    ext i
    simp only [Finset.mem_map,Equiv.toEmbedding_apply,mem_tupleNames]
    constructor
    · rintro ⟨k,⟨j,rfl⟩,rfl⟩
      exact ⟨j,(hσ j).symm⟩
    · rintro ⟨j,rfl⟩
      exact ⟨e j,⟨j,rfl⟩,hσ j⟩
  have ht := typeOf_permute S T (tupleNames e) σ.symm h
  simp only [Equiv.symm_symm,hn] at ht
  have hv : typeOf S (tupleNames (u.trans e')) v =
      typeOf S (tupleNames (u.trans e')) (tupleAssignment e (a ∘ u) ∘ σ.symm) := by
    apply typeOf_congr
    intro i hi
    obtain ⟨j,rfl⟩ := (mem_tupleNames _ _).mp hi
    change tupleAssignment e' a (e' (u j)) =
      tupleAssignment e (a ∘ u) (σ.symm (e' (u j)))
    rw [tupleAssignment_apply,← hσ j,σ.symm_apply_apply,tupleAssignment_apply]
    rfl
  obtain ⟨w',ht',hp⟩ := extend_type S T (tupleNames (u.trans e')) (tupleNames e')
    v w (hv.trans ht)
  have hs : tupleNames (u.trans e') ⊆ tupleNames e' := by
    intro i hi
    obtain ⟨j,rfl⟩ := (mem_tupleNames _ _).mp hi
    exact (mem_tupleNames _ _).mpr ⟨u j,rfl⟩
  rw [Finset.union_eq_right.mpr hs] at ht'
  refine ⟨fun j => w' (e' j),?_,?_⟩
  · funext j
    rw [Function.comp_apply,hp (e' (u j)) ((mem_tupleNames _ _).mpr ⟨j,rfl⟩),hw]
  · rw [tupleType_assignment T e' _ w' (fun _ => rfl)]
    exact ht'

end Tuple

section Append

variable {J D : Type*} [Fintype J] [Fintype D] [Fintype I]

variable [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]

theorem tupleType_append (S : Structure R A) (T : Structure R B)
    (e : J ↪ I) (e' : J ⊕ D ↪ I) (a : J → A) (b : J → B) (c : D → A)
    (h : tupleType S e a = tupleType T e b) :
    ∃ d : D → B, tupleType S e' (Sum.elim a c) = tupleType T e' (Sum.elim b d) := by
  obtain ⟨b',hb',ht⟩ := tupleType_extend S T e e' (Function.Embedding.inl)
    (Sum.elim a c) b h
  refine ⟨b' ∘ Sum.inr,?_⟩
  have heq : b' = Sum.elim b (b' ∘ Sum.inr) := by
    funext j
    cases j with
    | inl j => exact congrFun hb' j
    | inr j => rfl
  rw [heq] at ht
  exact ht

end Append

end

end WitnessedSeparation.Counting



namespace WitnessedSeparation.Grid

noncomputable section

open Classical Finset

variable {n : ℕ} {b b' : Vertex n → Scalar}

theorem AtomShift.classLabel {t : Edge n → Scalar} {x : Atom b} {y : Atom b'}
    (h : AtomShift t x y) : Grid.classLabel x = Grid.classLabel y := by
  cases h <;> simp [Grid.classLabel]

theorem AtomShift.analysisRelation {t : Edge n → Scalar} {x x' : Atom b} {y y' : Atom b'}
    (h : AtomShift t x y) (h' : AtomShift t x' y') (r : AnalysisSymbol) :
    (analysisStructure b).rel r x x' ↔ (analysisStructure b').rel r y y' := by
  cases r with
  | input r => exact h.relation_iff h'
  | preorder => change classIndex x ≤ classIndex x' ↔ classIndex y ≤ classIndex y'
                simp only [classIndex,h.classLabel,h'.classLabel]
  | raw d =>
    change rawDifference b d x x' ↔ rawDifference b' d y y'
    cases h <;> cases h' <;> simp only [rawDifference,shiftLocal_flow]
    rename_i e s f a
    constructor
    · rintro ⟨rfl,he⟩; exact ⟨rfl,by linear_combination he⟩
    · rintro ⟨rfl,he⟩; exact ⟨rfl,by linear_combination he⟩

theorem predecessors_recovers_class {x y : Atom b}
    (h : (predecessors x).card = (predecessors y).card) : classLabel x = classLabel y := by
  have hlt {x y : Atom b} (hxy : classIndex x < classIndex y) :
      (predecessors x).card < (predecessors y).card := by
    apply card_lt_card
    apply ssubset_iff_subset_ne.mpr
    refine ⟨?_,?_⟩
    · intro z hz; exact mem_filter.mpr ⟨mem_univ _,lt_trans (mem_filter.mp hz).2 hxy⟩
    · intro he
      have hx : x ∈ predecessors y := mem_filter.mpr ⟨mem_univ _,hxy⟩
      rw [←he] at hx
      exact (lt_irrefl _) (mem_filter.mp hx).2
  have hi : classIndex x = classIndex y := by
    rcases lt_trichotomy (classIndex x) (classIndex y) with hh | hh | hh
    · exact False.elim ((ne_of_lt (hlt hh)) h)
    · exact hh
    · exact False.elim ((ne_of_lt (hlt hh)) h.symm)
  exact (Fintype.equivFin (ClassLabel n)).injective hi

theorem free_classFormula {I : Type*} [DecidableEq I] (i j : I) (h : ℕ) :
    (classFormula i j h).free ⊆ {i} := by
  simp only [classFormula,Counting.Formula.free]
  intro k hk
  simp only [mem_erase,mem_union,mem_insert,mem_singleton] at hk ⊢
  tauto

theorem eval_classFormula {I : Type*} [DecidableEq I] (v : I → Atom b) {i j : I}
    (hne : i ≠ j) (h : ℕ) :
    (classFormula i j h).eval (analysisStructure b) v ↔ (predecessors (v i)).card = h := by
  have hh (x : Atom b) :
      ((analysisStructure b).rel .preorder (Function.update v j x j) (Function.update v j x i) ∧
      ¬(analysisStructure b).rel .preorder (Function.update v j x i) (Function.update v j x j)) ↔
      x ∈ predecessors (v i) := by
    simp only [analysisStructure,Function.update_self,Function.update_of_ne hne,
      predecessors,mem_filter,mem_univ,true_and,lt_iff_le_not_ge]
  change Nonempty (_ ≃ Fin h) ↔ _
  let e := Equiv.subtypeEquivRight hh
  constructor
  · rintro ⟨f⟩
    simpa using Fintype.card_congr (e.symm.trans f)
  · intro he
    exact ⟨e.trans ((Fintype.equivFin _).trans (finCongr (by simpa using he)))⟩

theorem type_recovers_classes {I : Type*} [DecidableEq I] (names : Finset I)
    {v w : I → Atom b} (ht : Counting.typeOf (analysisStructure b) names v =
      Counting.typeOf (analysisStructure b) names w) {i j : I} (hi : i ∈ names) (hne : i ≠ j) :
    classLabel (v i) = classLabel (w i) := by
  apply predecessors_recovers_class
  let h := (predecessors (v i)).card
  have hf : (classFormula i j h).free ⊆ names :=
    (free_classFormula i j h).trans (singleton_subset_iff.mpr hi)
  have he := (Counting.typeOf_eq_iff _ _ _ _ _).mp ht (classFormula i j h) hf
  exact ((eval_classFormula w hne h).mp (he.mp ((eval_classFormula v hne h).mpr rfl))).symm

end





noncomputable section

open Classical Finset

variable {n : ℕ} {b b' : Vertex n → Scalar}

theorem blockEdges_card (J : Block n) : (blockEdges J).card ≤ 6 := by
  cases J with
  | inl e => simp [blockEdges]
  | inr v =>
    have hh : (blockEdges (.inr v)).card = Fintype.card {e : Edge n // head e = v ∨ tail e = v} := by
      rw [←Fintype.card_coe]
      exact Fintype.card_congr (Equiv.subtypeEquivRight (fun e => by simp [blockEdges,incident]))
    rw [hh]
    exact degree_le_six v

theorem touch_card (x : Atom b) : (touch x).card ≤ 6 := blockEdges_card (atomBlock x)

theorem AtomShift.congr {t t' : Edge n → Scalar} {x : Atom b} {y : Atom b'}
    (h : AtomShift t x y) (he : ∀ e ∈ touch x, t e = t' e) : AtomShift t' x y := by
  cases h with
  | edge e s =>
    have hh := he e (by simp [touch,atomBlock,blockEdges])
    simpa only [hh] using (AtomShift.edge (b := b) (b' := b') (t := t') e s)
  | config v s h =>
    have hv : boundary t' v = b' v-b v := by
      rw [←sum_incident,←h,←sum_incident]
      apply sum_congr rfl
      intro e _
      rw [he e.val (by simpa [touch,atomBlock,blockEdges] using e.property)]
    have hs : s.shift t h = s.shift t' hv := by
      apply Configuration.ext
      intro e
      simp only [Configuration.shift_state,he e.val (by simpa [touch,atomBlock,blockEdges] using e.property)]
    rw [hs]
    exact .config v s hv

theorem touches_card {I : Type*} [DecidableEq I] (names : Finset I) (v : I → Atom b) :
    (touches names v).card ≤ 6*names.card := by
  calc
    _ ≤ ∑ i ∈ names, (touch (v i)).card := card_biUnion_le
    _ ≤ ∑ _ ∈ names, 6 := sum_le_sum (fun i _ => touch_card (v i))
    _ = 6*names.card := by simp [Nat.mul_comm]

theorem touch_subset_touches {I : Type*} [DecidableEq I] (names : Finset I)
    (v : I → Atom b) {i : I} (hi : i ∈ names) : touch (v i) ⊆ touches names v := by
  intro e he; exact mem_biUnion.mpr ⟨i,hi,he⟩

theorem touches_mono {I : Type*} [DecidableEq I] {s t : Finset I} (hst : s ⊆ t)
    (v : I → Atom b) : touches s v ⊆ touches t v := by
  intro e he
  obtain ⟨i,hi,he⟩ := mem_biUnion.mp he
  exact mem_biUnion.mpr ⟨i,hst hi,he⟩

theorem touches_insert_update {I : Type*} [DecidableEq I] (names : Finset I)
    (v : I → Atom b) (i : I) (a : Atom b) :
    touches (insert i (names.erase i)) (Function.update v i a) =
      touches (names.erase i) v ∪ touch a := by
  ext e
  simp only [touches,mem_biUnion,mem_insert,mem_erase,mem_union]
  constructor
  · rintro ⟨j,(rfl | hj),he⟩
    · exact Or.inr (by simpa using he)
    · exact Or.inl ⟨j,hj,by simpa [Function.update_of_ne hj.1] using he⟩
  · rintro (⟨j,hj,he⟩ | he)
    · exact ⟨j,Or.inr hj,by simpa [Function.update_of_ne hj.1] using he⟩
    · exact ⟨i,Or.inl rfl,by simpa using he⟩

end





noncomputable section

open Classical Finset

variable {n : ℕ} {b : Vertex n → Scalar}

theorem hasState_stateAt (x : Atom b) (e : Edge n) (he : e ∈ touch x) :
    HasState x e (stateAt x e he) := by
  cases x with
  | inl x =>
    rcases x with ⟨f,s⟩
    have hh : e = f := by simpa [touch,atomBlock,blockEdges] using he
    subst e
    simp
  | inr x =>
    rcases x with ⟨v,s⟩
    exact (hasState_config _ _ _ _).mpr ⟨by simpa [touch,atomBlock,blockEdges] using he,rfl⟩

theorem classLabel_edge_iff (y : Atom b) (e : Edge n) (u : EdgeFaces e → Support.Plane) :
    classLabel y = .inl ⟨e,u⟩ ↔ ∃ t : LocalGroup e, y = .inl ⟨e,t⟩ ∧ t.face = u := by
  cases y with
  | inl y =>
    rcases y with ⟨f,s⟩
    constructor
    · intro h
      have hh := Sum.inl.inj h
      have hf := congrArg Sigma.fst hh
      dsimp at hf
      subst f
      have hu := (Sigma.mk.inj_iff.mp hh).2
      exact ⟨s,rfl,eq_of_heq hu⟩
    · rintro ⟨t,h,rfl⟩; cases h; rfl
  | inr y => simp [classLabel]

theorem atomShift_of_states (x y : Atom b) (t : Edge n → Scalar)
    (hc : classLabel x = classLabel y)
    (hs : ∀ e (he : e ∈ touch x), HasState y e (shiftLocal e (t e) (stateAt x e he))) :
    AtomShift t x y := by
  cases x with
  | inl x =>
    rcases x with ⟨e,s⟩
    obtain ⟨s',rfl,hface⟩ := (classLabel_edge_iff y e s.face).mp hc.symm
    have h := hs e (by simp [touch,atomBlock,blockEdges])
    simp only [hasState_edge] at h
    have hh : s' = shiftLocal e (t e) s := eq_of_heq (Sigma.mk.inj_iff.mp h).2
    subst s'
    exact .edge e s
  | inr x =>
    rcases x with ⟨v,s⟩
    cases y with
    | inl y => cases hc
    | inr y =>
      rcases y with ⟨w,s'⟩
      have hw := congrArg Sigma.fst (Sum.inr.inj hc)
      dsimp at hw
      subst w
      have hstates : s'.state = shiftStates t s.state := by
        funext e
        have he : e.val ∈ touch (.inr ⟨v,s⟩) := by simpa [touch,atomBlock,blockEdges] using e.property
        obtain ⟨h,hval⟩ := (hasState_config _ _ _ _).mp (hs e.val he)
        exact hval
      have hb : boundary t v = b v-b v := by
        have h := s'.charge
        rw [hstates,shiftStates_divergence,s.charge] at h
        linear_combination h
      have hy : s' = s.shift t hb := by
        apply Configuration.ext
        intro e
        exact congrFun hstates e
      rw [hy]
      exact .config v s hb

theorem augmented_diagram_shift {J : Type*} (a a' : J → Atom b)
    (y : Occurrences a → Atom b) (h : SameDiagram (Augment a) (Sum.elim a' y)) :
    ∃ t : Edge n → Scalar, ∀ j, AtomShift t (a j) (a' j) := by
  have hy (o : Occurrences a) : ∃ s : LocalGroup o.2.val,
      y o = .inl ⟨o.2.val,s⟩ ∧ s.face = (stateAt (a o.1) o.2.val o.2.property).face :=
    (classLabel_edge_iff _ _ _).mp (h.classes (.inr o)).symm
  choose target htarget hface using hy
  let delta (o : Occurrences a) : Scalar :=
    (target o).flow-(stateAt (a o.1) o.2.val o.2.property).flow
  have hd (o p : Occurrences a) (he : o.2.val = p.2.val) : delta o = delta p := by
    have hh := (h.relation (.raw
      ((stateAt (a p.1) p.2.val p.2.property).flow -
        (stateAt (a o.1) o.2.val o.2.property).flow)) (.inr o) (.inr p)).mp
      (show (analysisStructure b).rel _ (Augment a (.inr o)) (Augment a (.inr p)) from ⟨he,rfl⟩)
    change rawDifference b _ (y o) (y p) at hh
    rw [htarget o,htarget p] at hh
    have hh' := hh.2
    dsimp [delta]
    linear_combination -hh'
  let t (e : Edge n) : Scalar := if he : ∃ o : Occurrences a, o.2.val = e
    then delta he.choose else 0
  have ht (o : Occurrences a) : t o.2.val = delta o := by
    have he : ∃ p : Occurrences a, p.2.val = o.2.val := ⟨o,rfl⟩
    simp only [t,dite_eq_left he]
    exact hd he.choose o he.choose_spec
  have heq (o : Occurrences a) :
      target o = shiftLocal o.2.val (t o.2.val) (stateAt (a o.1) o.2.val o.2.property) := by
    apply Support.H.ext
    · simpa only [shiftLocal_face] using hface o
    · simp only [shiftLocal_flow,ht,delta]; abel
  refine ⟨t,fun j => atomShift_of_states _ _ _ (h.classes (.inl j)) ?_⟩
  intro e he
  let o : Occurrences a := ⟨j,e,he⟩
  have hs := hasState_stateAt (a j) e he
  have hh : a' j = y o ∨ AtomRelation b .I (a' j) (y o) :=
    hs.elim (fun hh => Or.inl ((h.equal (.inl j) (.inr o)).mp hh))
      (fun hh => Or.inr ((h.relation (.input .I) (.inl j) (.inr o)).mp hh))
  rw [htarget o,heq o] at hh
  exact hh

end





noncomputable section

open Classical Finset

variable {n : ℕ} {b : Vertex n → Scalar}

variable {J I : Type*} [Fintype J] [Fintype I] [DecidableEq I] [Nonempty (Atom b)]

omit [Fintype I] in
theorem sameDiagram_of_type (names : J ↪ I) (a a' : J → Atom b)
    (ht : Counting.tupleType (analysisStructure b) names a =
      Counting.tupleType (analysisStructure b) names a')
    (spare : I) (hsp : spare ∉ Counting.tupleNames names) : SameDiagram a a' := by
  have hmem (j : J) : names j ∈ Counting.tupleNames names := by simp
  refine ⟨?_,?_,?_⟩
  · intro j
    have hn : names j ≠ spare := by intro h; exact hsp (h ▸ hmem j)
    have hh := type_recovers_classes (Counting.tupleNames names) ht (hmem j) hn
    simpa only [Counting.tupleAssignment_apply] using hh
  · intro i j
    have hh := (Counting.typeOf_eq_iff _ _ _ _ _).mp ht
      (.equal (names i) (names j)) (by change ({names i,names j} : Finset I) ⊆ Counting.tupleNames names; exact insert_subset_iff.mpr ⟨hmem i,singleton_subset_iff.mpr (hmem j)⟩)
    simpa only [Counting.Formula.eval,Counting.tupleAssignment_apply] using hh
  · intro r i j
    have hh := (Counting.typeOf_eq_iff _ _ _ _ _).mp ht
      (.relation r (names i) (names j)) (by change ({names i,names j} : Finset I) ⊆ Counting.tupleNames names; exact insert_subset_iff.mpr ⟨hmem i,singleton_subset_iff.mpr (hmem j)⟩)
    simpa only [Counting.Formula.eval,Counting.tupleAssignment_apply] using hh

end

end WitnessedSeparation.Grid

end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_Homogeneity
attribute [-instance] _root_.OAI.WitnessedSeparation.Forms.instFintypeElemHFLabelValues _root_.OAI.WitnessedSeparation.Forms.instFintypeMolecules
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace WitnessedSeparation.Grid

noncomputable section

open Classical Finset

variable {n : ℕ} {b : Vertex n → Scalar}

variable {J : Type*} [Fintype J]

theorem occurrences_card (a : J → Atom b) : Fintype.card (Occurrences a) ≤ 6*Fintype.card J := by
  rw [Fintype.card_sigma]
  calc
    _ = ∑ j : J, (touch (a j)).card := by congr 1; ext j; exact Fintype.card_coe _
    _ ≤ ∑ _ : J, 6 := sum_le_sum (fun j _ => touch_card (a j))
    _ = _ := by simp [Nat.mul_comm]

theorem augment_card (a : J → Atom b) : Fintype.card (J ⊕ Occurrences a) ≤ 7*Fintype.card J := by
  rw [Fintype.card_sum]
  have := occurrences_card a
  omega

theorem namesBelow_spare {P : Type*} [Fintype P] {M : ℕ} (h : Fintype.card P < M) :
    (⟨Fintype.card P,h⟩ : Fin M) ∉ Counting.tupleNames (namesBelow h) := by
  intro hh
  obtain ⟨j,hj⟩ := (Counting.mem_tupleNames _ _).mp hh
  have hv := congrArg Fin.val hj
  change (Fintype.equivFin P j).val = Fintype.card P at hv
  exact (Fintype.equivFin P j).isLt.ne hv

theorem tuple_partial_shift {M : ℕ} [Nonempty (Atom b)] (names : J ↪ Fin M)
    (a a' : J → Atom b) (hw : 7*Fintype.card J < M)
    (ht : Counting.tupleType (analysisStructure b) names a =
      Counting.tupleType (analysisStructure b) names a') :
    ∃ t : Edge n → Scalar, ∀ j, AtomShift t (a j) (a' j) := by
  have hcard : Fintype.card (J ⊕ Occurrences a) < M := lt_of_le_of_lt (augment_card a) hw
  obtain ⟨y,hy⟩ := Counting.tupleType_append (analysisStructure b) (analysisStructure b)
    names (namesBelow hcard) a a' (occurrenceAtom a) ht
  exact augmented_diagram_shift a a' y
    (sameDiagram_of_type _ _ _ hy ⟨_,hcard⟩ (namesBelow_spare hcard))

theorem AtomShift.stateAt_flow {t : Edge n → Scalar} {x y : Atom b}
    (h : AtomShift t x y) (e : Edge n) (he : e ∈ touch x) :
    (stateAt y e (by rw [←touch_shift h]; exact he)).flow =
      t e + (stateAt x e he).flow := by
  cases h with
  | edge f s =>
    have hef : e = f := by simpa [touch,atomBlock,blockEdges] using he
    subst e
    simp only [stateAt_edge (b := b),shiftLocal_flow]
  | config v s h =>
    have hi : incident v e := by simpa [touch,atomBlock,blockEdges] using he
    change ((s.shift t h).state ⟨e,hi⟩).flow = t e + (s.state ⟨e,hi⟩).flow
    simp

theorem AtomShift.unique_on_touch {t u : Edge n → Scalar} {x y : Atom b}
    (ht : AtomShift t x y) (hu : AtomShift u x y) (e : Edge n) (he : e ∈ touch x) :
    t e = u e := by
  have hh := (ht.stateAt_flow e he).symm.trans (hu.stateAt_flow e he)
  exact add_right_cancel hh

end

end WitnessedSeparation.Grid



namespace WitnessedSeparation.Projection

open Finset

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

variable [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

private theorem ind_sq {α : Type*} [DecidableEq α] (S : Finset α) (a : α) :
    ind S a ^ 2 = ind S a := by simp [ind]

private theorem sum_ind {α : Type*} [DecidableEq α] [Fintype α] (S : Finset α) :
    ∑ a, ind S a = S.card := by simp [ind]

theorem card_sq_le_projections (R : Finset (X × Y × Z)) :
    R.card^2 ≤ (R.image (fun v => (v.1,v.2.1))).card *
      (R.image (fun v => (v.1,v.2.2))).card * (R.image (fun v => (v.2.1,v.2.2))).card := by
  let A := R.image (fun v => (v.1,v.2.1))
  let B := R.image (fun v => (v.1,v.2.2))
  let D := R.image (fun v => (v.2.1,v.2.2))
  let a (p : X × Y) := ind A p
  let b (p : X × Z) := ind B p
  let d (p : Y × Z) := ind D p
  let c (p : X × Y) := ∑ k, b (p.1,k) * d (p.2,k)
  have hr : R.card ≤ ∑ p, a p * c p := by
    rw [←sum_ind R]
    simp only [Fintype.sum_prod_type]
    dsimp [c]
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro k _
    dsimp [a,b,d]
    by_cases h : (i,j,k) ∈ R
    · have ha : (i,j) ∈ A := mem_image.mpr ⟨(i,j,k),h,rfl⟩
      have hb : (i,k) ∈ B := mem_image.mpr ⟨(i,j,k),h,rfl⟩
      have hd : (j,k) ∈ D := mem_image.mpr ⟨(i,j,k),h,rfl⟩
      simp [ind,h,ha,hb,hd]
    · simp [ind,h]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s := (univ : Finset (X × Y))) a c
  have ha : ∑ p : X × Y, a p^2 = A.card := by simp only [a,ind_sq,sum_ind]
  have hc : ∑ p : X × Y, c p^2 ≤ B.card * D.card := by
    calc
      _ ≤ ∑ p : X × Y, (∑ k, b (p.1,k)^2) * (∑ k, d (p.2,k)^2) := by
        apply Finset.sum_le_sum
        intro p _
        exact Finset.sum_mul_sq_le_sq_mul_sq univ (fun k => b (p.1,k)) (fun k => d (p.2,k))
      _ = B.card * D.card := by
        simp only [b,d,ind_sq,Fintype.sum_prod_type]
        rw [←Finset.sum_mul_sum]
        rw [←Fintype.sum_prod_type,←Fintype.sum_prod_type,sum_ind,sum_ind]
  calc
    R.card^2 ≤ (∑ p, a p*c p)^2 := Nat.pow_le_pow_left hr 2
    _ ≤ (∑ p, a p^2) * ∑ p, c p^2 := hcs
    _ ≤ A.card * (B.card*D.card) := by rw [ha]; exact Nat.mul_le_mul_left _ hc
    _ = _ := by dsimp [A,B,D]; simp only [mul_assoc]

end WitnessedSeparation.Projection



namespace WitnessedSeparation.BoxLines

open Finset

variable {J : Type*} [Fintype J] [DecidableEq J] {n : ℕ}

private theorem fin_constant {P : Fin (n+1) → Prop}
    (h : ∀ i : Fin n, P i.castSucc ↔ P i.succ) (i : Fin (n+1)) : P i ↔ P 0 := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih => exact (h i).symm.trans ih

theorem partial_line_boundary (R : Finset (Fin (n+1) × J)) {j : J}
    (hj : j ∈ projection R \ fullLines R) :
    ∃ i : Fin n, (i,j) ∈ edgeBoundary R := by
  classical
  by_contra hn
  have h : ∀ i : Fin n, (i.castSucc,j) ∈ R ↔ (i.succ,j) ∈ R := by
    intro i
    by_contra hh
    exact hn ⟨i,by simp [edgeBoundary,hh]⟩
  obtain ⟨hj,hf⟩ := mem_sdiff.mp hj
  obtain ⟨⟨i,j'⟩,hi,he⟩ := mem_image.mp hj
  dsimp at he
  subst j'
  have hzero := (fin_constant (P := fun i => (i,j) ∈ R) h i).mp hi
  apply hf
  simp only [fullLines,mem_filter,mem_univ,true_and]
  intro i
  exact (fin_constant (P := fun i => (i,j) ∈ R) h i).mpr hzero

theorem line_count (R : Finset (Fin (n+1) × J)) :
    (n+1) * (projection R).card ≤ (n+1) * (edgeBoundary R).card + R.card := by
  classical
  have hF : fullLines R ⊆ projection R := by
    intro j hj
    have h := (mem_filter.mp hj).2
    exact mem_image.mpr ⟨(0,j),h 0,rfl⟩
  have hfull : (n+1) * (fullLines R).card ≤ R.card := by
    have hh : (univ : Finset (Fin (n+1))) ×ˢ fullLines R ⊆ R := by
      rintro ⟨i,j⟩ hp
      exact (mem_filter.mp (mem_product.mp hp).2).2 i
    simpa only [card_product,card_univ,Fintype.card_fin] using card_le_card hh
  have hpartial : (projection R \ fullLines R).card ≤ (edgeBoundary R).card := by
    have hh : projection R \ fullLines R ⊆ (edgeBoundary R).image Prod.snd := by
      intro j hj
      obtain ⟨i,hi⟩ := partial_line_boundary R hj
      exact mem_image.mpr ⟨(i,j),hi,rfl⟩
    exact (card_le_card hh).trans card_image_le
  have hc := card_sdiff_add_card_eq_card hF
  calc
    (n+1) * (projection R).card =
        (n+1) * (projection R \ fullLines R).card + (n+1) * (fullLines R).card := by
      rw [←hc,Nat.mul_add]
    _ ≤ (n+1) * (edgeBoundary R).card + R.card :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hpartial) hfull

end WitnessedSeparation.BoxLines



namespace WitnessedSeparation.Grid

open Finset

variable {n : ℕ}

theorem swapXY_injective : Function.Injective (@swapXY n) := by
  rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h
  simp only [swapXY,Prod.mk.injEq] at h ⊢
  tauto

theorem moveZ_injective : Function.Injective (@moveZ n) := by
  rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h
  simp only [moveZ,Prod.mk.injEq] at h ⊢
  tauto

private theorem boundary_x_le (R : Finset (Vertex n)) :
    (BoxLines.edgeBoundary R).card ≤ (edgeBoundary R).card := by
  apply card_le_card_of_injOn (fun p => ex p.1 p.2.1 p.2.2)
  · rintro ⟨i,j,k⟩ hp
    have hp' := (Finset.mem_filter.mp (show (i,j,k) ∈ BoxLines.edgeBoundary R from hp)).2
    apply Finset.mem_filter.mpr
    exact ⟨mem_univ _,hp'⟩
  · intro p _ q _ h
    exact Sum.inl.inj h

private theorem boundary_y_le (R : Finset (Vertex n)) :
    (BoxLines.edgeBoundary (R.image swapXY)).card ≤ (edgeBoundary R).card := by
  apply card_le_card_of_injOn (fun p => ey p.2.1 p.1 p.2.2)
  · rintro ⟨j,i,k⟩ hp
    have he (v : Vertex n) : swapXY v ∈ R.image swapXY ↔ v ∈ R :=
      by
        constructor
        · intro h
          obtain ⟨w,hw,he⟩ := mem_image.mp h
          simpa only [swapXY_injective he] using hw
        · intro h; exact mem_image.mpr ⟨v,h,rfl⟩
    have h1 := he (i,j.castSucc,k)
    have h2 := he (i,j.succ,k)
    have hp' := (Finset.mem_filter.mp (show (j,i,k) ∈ BoxLines.edgeBoundary (R.image swapXY) from hp)).2
    apply Finset.mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    change ¬ ((i,j.castSucc,k) ∈ R ↔ (i,j.succ,k) ∈ R)
    change ¬(swapXY (i,j.castSucc,k) ∈ R.image swapXY ↔ swapXY (i,j.succ,k) ∈ R.image swapXY) at hp'
    simpa only [he] using hp'
  · rintro ⟨j,i,k⟩ _ ⟨j',i',k'⟩ _ h
    simp only [ey,Sum.inr.injEq,Sum.inl.injEq,Prod.mk.injEq] at h ⊢
    tauto

private theorem boundary_z_le (R : Finset (Vertex n)) :
    (BoxLines.edgeBoundary (R.image moveZ)).card ≤ (edgeBoundary R).card := by
  apply card_le_card_of_injOn (fun p => ez p.2.1 p.2.2 p.1)
  · rintro ⟨k,i,j⟩ hp
    have he (v : Vertex n) : moveZ v ∈ R.image moveZ ↔ v ∈ R :=
      by
        constructor
        · intro h
          obtain ⟨w,hw,he⟩ := mem_image.mp h
          simpa only [moveZ_injective he] using hw
        · intro h; exact mem_image.mpr ⟨v,h,rfl⟩
    have h1 := he (i,j,k.castSucc)
    have h2 := he (i,j,k.succ)
    have hp' := (Finset.mem_filter.mp (show (k,i,j) ∈ BoxLines.edgeBoundary (R.image moveZ) from hp)).2
    apply Finset.mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    change ¬ ((i,j,k.castSucc) ∈ R ↔ (i,j,k.succ) ∈ R)
    change ¬(moveZ (i,j,k.castSucc) ∈ R.image moveZ ↔ moveZ (i,j,k.succ) ∈ R.image moveZ) at hp'
    simpa only [he] using hp'
  · rintro ⟨k,i,j⟩ _ ⟨k',i',j'⟩ _ h
    simp only [ez,Sum.inr.injEq,Prod.mk.injEq] at h ⊢
    tauto

theorem projection_line_bounds (R : Finset (Vertex n)) :
    let A := (R.image fun v => (v.1,v.2.1)).card
    let B := (R.image fun v => (v.1,v.2.2)).card
    let D := (R.image fun v => (v.2.1,v.2.2)).card
    (n+1)*A ≤ (n+1)*(edgeBoundary R).card + R.card ∧
    (n+1)*B ≤ (n+1)*(edgeBoundary R).card + R.card ∧
    (n+1)*D ≤ (n+1)*(edgeBoundary R).card + R.card := by
  have hx := (BoxLines.line_count R).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left (n+1) (boundary_x_le R)) _)
  have hy := (BoxLines.line_count (R.image swapXY)).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left (n+1) (boundary_y_le R)) _)
  have hz := (BoxLines.line_count (R.image moveZ)).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left (n+1) (boundary_z_le R)) _)
  simp only [card_image_of_injective _ swapXY_injective,BoxLines.projection,
    image_image,Function.comp_def,swapXY] at hy
  simp only [card_image_of_injective _ moveZ_injective,BoxLines.projection,
    image_image,Function.comp_def,moveZ] at hz
  exact ⟨hz,hy,hx⟩

end WitnessedSeparation.Grid



namespace WitnessedSeparation.Grid

theorem boxConstant_pos : 0 < boxConstant := by
  unfold boxConstant
  have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ) < 2)
    (by norm_num : -(1:ℝ)/3 < 0)
  simpa using h

private theorem boundary_algebra {L r d p : ℝ} (hL : 0 < L) (hr : 0 < r)
    (_hd : 0 ≤ d) (hp : 0 ≤ p) (hhalf : 2*r ≤ L^3)
    (hproj : r^2 ≤ p^3) (hline : L*p ≤ L*d+r) :
    boxConstant * r^((2:ℝ)/3) ≤ d := by
  have hr0 := le_of_lt hr
  have h23 : (r^((2:ℝ)/3))^3 = r^2 := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hr0]
    norm_num
  have h13 : (r^((1:ℝ)/3))^3 = r := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hr0]
    norm_num
  have hc3 : ((2:ℝ)^(-(1:ℝ)/3))^3 = (1:ℝ)/2 := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have hc : 0 ≤ (2:ℝ)^(-(1:ℝ)/3) := Real.rpow_nonneg (by norm_num) _
  have hp' : r^((2:ℝ)/3) ≤ p := by
    apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg hr0 _) hp (by norm_num : (3:ℕ) ≠ 0)).mp
    simpa only [h23] using hproj
  have hl' : r^((1:ℝ)/3) ≤ (2:ℝ)^(-(1:ℝ)/3)*L := by
    apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg hr0 _)
      (mul_nonneg hc hL.le) (by norm_num : (3:ℕ) ≠ 0)).mp
    rw [h13,mul_pow,hc3]
    linarith
  have hprod : r^((1:ℝ)/3)*r^((2:ℝ)/3) = r := by
    rw [←Real.rpow_add hr]
    norm_num
  have hsmall := mul_le_mul_of_nonneg_right hl' (Real.rpow_nonneg hr0 ((2:ℝ)/3))
  rw [hprod] at hsmall
  have hproj' := mul_le_mul_of_nonneg_left hp' hL.le
  unfold boxConstant
  nlinarith

theorem box_boundary {n : ℕ} (R : Finset (Vertex n)) (hne : R.Nonempty)
    (hhalf : 2*R.card ≤ (n+1)^3) :
    boxConstant * (R.card:ℝ)^((2:ℝ)/3) ≤ (edgeBoundary R).card := by
  let A := (R.image fun v => (v.1,v.2.1)).card
  let B := (R.image fun v => (v.1,v.2.2)).card
  let D := (R.image fun v => (v.2.1,v.2.2)).card
  let p := max A (max B D)
  have ha : A ≤ p := le_max_left _ _
  have hb : B ≤ p := (le_max_left B D).trans (le_max_right _ _)
  have hd : D ≤ p := (le_max_right B D).trans (le_max_right _ _)
  have hp : R.card^2 ≤ p^3 := by
    calc
      _ ≤ A*B*D := Projection.card_sq_le_projections R
      _ ≤ p*p*p := Nat.mul_le_mul (Nat.mul_le_mul ha hb) hd
      _ = p^3 := by ring
  obtain ⟨hA,hB,hD⟩ := projection_line_bounds R
  have hline : (n+1)*p ≤ (n+1)*(edgeBoundary R).card + R.card := by
    dsimp [p]
    rw [mul_max_of_nonneg _ _ (Nat.zero_le _),mul_max_of_nonneg _ _ (Nat.zero_le _)]
    exact max_le hA (max_le hB hD)
  apply boundary_algebra (L := (n+1:ℕ)) (p := p)
  · positivity
  · exact_mod_cast Finset.card_pos.mpr hne
  · positivity
  · positivity
  · exact_mod_cast hhalf
  · exact_mod_cast hp
  · exact_mod_cast hline

end WitnessedSeparation.Grid



namespace WitnessedSeparation.Flows

noncomputable section

open Classical

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

variable (tail head : E → V) (T : Finset E)

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem edge_connected (e : E) (he : e ∉ T) :
    (connected tail head T).r (tail e) (head e) :=
  Relation.EqvGen.rel _ _ ⟨e,he,rfl,rfl⟩

omit [Fintype V] in
theorem path_flow {v w : V} (h : (connected tail head T).r v w) :
    ∃ t : E → Scalar, (∀ e ∈ T, t e = 0) ∧
      incidence tail head t = Pi.single w 1 - Pi.single v 1 := by
  induction h with
  | rel v w h =>
    obtain ⟨e,he,rfl,rfl⟩ := h
    refine ⟨Pi.single e 1,?_,incidence_single tail head e 1⟩
    intro f hf
    exact Pi.single_eq_of_ne (by intro h; subst f; exact he hf) _
  | refl v => exact ⟨0,by simp,by simp⟩
  | symm v w h ih =>
    obtain ⟨t,ht,hd⟩ := ih
    refine ⟨-t,by simpa using ht,?_⟩
    rw [map_neg,hd]; abel
  | trans u v w _ _ ih ih' =>
    obtain ⟨t,ht,hd⟩ := ih
    obtain ⟨t',ht',hd'⟩ := ih'
    refine ⟨t+t',fun e he => by simp [ht e he,ht' e he],?_⟩
    rw [map_add,hd,hd']; abel

omit [Fintype V] in
private theorem sum_single (U : Finset V) (v : V) (z : Scalar) :
    ∑ x ∈ U, (Pi.single v z : V → Scalar) x = if v ∈ U then z else 0 := by
  simp [Pi.single_apply]

omit [DecidableEq E] in
theorem sum_incidence (t : E → Scalar) : ∑ v, incidence tail head t v = 0 := by
  change (∑ v, (∑ e, t e • (Pi.single (head e) 1 - Pi.single (tail e) 1) : V → Scalar) v) = _
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.sub_apply,mul_sub]
  rw [Finset.sum_comm]
  have h (e : E) : ∑ v, (t e * (Pi.single (head e) (1:Scalar) : V → Scalar) v -
      t e * (Pi.single (tail e) (1:Scalar) : V → Scalar) v) = 0 := by
    rw [Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.mul_sum]
    simp [Pi.single_apply]
  simp only [h,Finset.sum_const_zero]

theorem sum_incidence_component (t : E → Scalar) (ht : ∀ e ∈ T, t e = 0) (v : V) :
    ∑ w ∈ component tail head T v, incidence tail head t w = 0 := by
  change (∑ w ∈ component tail head T v,
    (∑ e, t e • (Pi.single (head e) 1 - Pi.single (tail e) 1) : V → Scalar) w) = _
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.sub_apply,mul_sub]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro e _
  rw [Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.mul_sum,sum_single,sum_single]
  by_cases he : e ∈ T
  · simp [ht e he]
  have hc : head e ∈ component tail head T v ↔ tail e ∈ component tail head T v := by
    simp only [mem_component]
    exact ⟨fun h => (connected tail head T).trans h ((connected tail head T).symm (edge_connected tail head T e he)),
      fun h => (connected tail head T).trans h (edge_connected tail head T e he)⟩
  simp only [hc,sub_self]

theorem solvable_iff (b : V → Scalar) :
    (∃ t : E → Scalar, (∀ e ∈ T, t e = 0) ∧ incidence tail head t = b) ↔
      ∀ v, ∑ w ∈ component tail head T v, b w = 0 := by
  constructor
  · rintro ⟨t,ht,rfl⟩
    exact sum_incidence_component tail head T t ht
  · intro hb
    let q : V → Component tail head T := Quotient.mk (connected tail head T)
    let : Fintype (Component tail head T) := Fintype.ofFinite _
    have hp (v : V) : ∃ t : E → Scalar, (∀ e ∈ T, t e = 0) ∧
        incidence tail head t = Pi.single v 1 - Pi.single ((q v).out) 1 := by
      apply path_flow tail head T
      exact Quotient.exact (Quotient.out_eq (q v))
    choose t ht hd using hp
    refine ⟨∑ v, b v • t v,?_,?_⟩
    · intro e he
      simp [Finset.sum_apply,ht _ e he]
    · rw [map_sum]
      simp only [map_smul,hd,smul_sub,Finset.sum_sub_distrib]
      have hfirst : (∑ v, b v • (Pi.single v (1:Scalar) : V → Scalar)) = b := by
        funext j; simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply]
      have hsecond : (∑ v, b v • (Pi.single (q v).out (1:Scalar) : V → Scalar)) = 0 := by
        rw [←Fintype.sum_fiberwise q]
        apply Finset.sum_eq_zero
        intro c _
        have hf : (∑ v : {v : V // q v = c}, b v) = 0 := by
          have he (v : V) : q v = c ↔ v ∈ component tail head T c.out := by
            rw [mem_component]
            constructor
            · intro h
              exact Quotient.exact ((Quotient.out_eq c).trans h.symm)
            · intro h
              exact (Quotient.sound h).symm.trans (Quotient.out_eq c)
          let ee := Equiv.subtypeEquivRight he
          have hs := Fintype.sum_equiv ee (fun v : {v : V // q v = c} => b v)
            (fun v : component tail head T c.out => b v) (fun _ => rfl)
          rw [hs]
          exact (Finset.sum_coe_sort (component tail head T c.out) b).trans (hb c.out)
        have hx : (∑ v : {v : V // q v = c}, b v •
            (Pi.single (q v).out (1:Scalar) : V → Scalar)) =
            (∑ v : {v : V // q v = c}, b v) • Pi.single c.out 1 := by
          rw [Finset.sum_smul]
          apply Finset.sum_congr rfl
          intro v _; rw [v.2]
        rw [hx,hf,zero_smul]
      rw [hfirst,hsecond,sub_zero]

theorem partial_flow_iff (σ : E → Scalar) :
    (∃ k : E → Scalar, incidence tail head k = 0 ∧ ∀ e ∈ T, k e = σ e) ↔
      ∀ v, ∑ w ∈ component tail head T v,
        incidence tail head (fun e => if e ∈ T then σ e else 0) w = 0 := by
  let z : E → Scalar := fun e => if e ∈ T then σ e else 0
  constructor
  · rintro ⟨k,hk,he⟩ v
    have ht : ∀ e ∈ T, (k-z) e = 0 := by intro e h; simp [z,h,he e h]
    have h := sum_incidence_component tail head T (k-z) ht v
    simpa [map_sub,hk,Finset.sum_neg_distrib] using h
  · intro h
    have hb : ∀ v, ∑ w ∈ component tail head T v, (-incidence tail head z) w = 0 := by
      intro v; simpa [Finset.sum_neg_distrib] using congrArg Neg.neg (h v)
    obtain ⟨t,ht,hd⟩ := (solvable_iff tail head T (-incidence tail head z)).mpr hb
    refine ⟨z+t,by simp [hd],?_⟩
    intro e he; simp [z,he,ht e he]

end





noncomputable section

open Classical Finset

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

variable (tail head : E → V) (T : Finset E)

omit [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem cell_nonempty (c : Component tail head T) : (cell tail head T c).Nonempty :=
  ⟨c.out,(mem_cell tail head T c c.out).mpr (Quotient.out_eq c)⟩

omit [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem cells_disjoint {c d : Component tail head T} (h : c ≠ d) :
    Disjoint (cell tail head T c) (cell tail head T d) := by
  apply disjoint_left.mpr
  intro v hc hd
  exact h ((mem_cell tail head T c v).mp hc |>.symm.trans ((mem_cell tail head T d v).mp hd))

omit [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem sum_cells {M : Type*} [AddCommMonoid M] (f : V → M) :
    ∑ c : Component tail head T, ∑ v ∈ cell tail head T c, f v = ∑ v, f v := by
  have he (c : Component tail head T) :
      (∑ v ∈ cell tail head T c, f v) = ∑ v, if quotientMap tail head T v = c then f v else 0 := by
    rw [←sum_filter]
    congr 1
    ext v; simp
  simp only [he]
  rw [sum_comm]
  simp

omit [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem sum_card_cells : ∑ c : Component tail head T, (cell tail head T c).card = Fintype.card V := by
  simpa using sum_cells tail head T (fun _ => (1:ℕ))

theorem boundary_cell_subset (c : Component tail head T) :
    edgeBoundary tail head (cell tail head T c) ⊆ T := by
  intro e he
  by_contra hn
  have hc := edge_connected tail head T e hn
  have hq : quotientMap tail head T (tail e) = quotientMap tail head T (head e) := Quotient.sound hc
  have hh := (mem_filter.mp he).2
  exact hh (by simp only [mem_cell,hq])

theorem sum_boundary_cells :
    ∑ c : Component tail head T, (edgeBoundary tail head (cell tail head T c)).card ≤ 2*T.card := by
  have he (c : Component tail head T) :
      (edgeBoundary tail head (cell tail head T c)).card =
      ∑ e ∈ T, if e ∈ edgeBoundary tail head (cell tail head T c) then 1 else 0 := by
    rw [←card_filter]
    congr 1
    ext e
    simp only [mem_filter]
    exact ⟨fun h => ⟨boundary_cell_subset tail head T c h,h⟩,fun h => h.2⟩
  simp only [he]
  rw [sum_comm]
  calc
    _ ≤ ∑ _ ∈ T, 2 := by
      apply sum_le_sum
      intro e _
      calc
        _ ≤ ∑ c : Component tail head T,
            ((if quotientMap tail head T (tail e) = c then 1 else 0) +
             (if quotientMap tail head T (head e) = c then 1 else 0)) := by
          apply sum_le_sum
          intro c _
          simp only [edgeBoundary,mem_filter,mem_univ,true_and,mem_cell]
          by_cases h1 : quotientMap tail head T (tail e) = c <;>
            by_cases h2 : quotientMap tail head T (head e) = c <;> simp [h1,h2]
        _ = 2 := by rw [sum_add_distrib]; simp
    _ = 2*T.card := by simp [mul_comm]

omit [Fintype E] [DecidableEq E] in


theorem small_failing_component (b : V → Scalar) (hb : ∑ v, b v = 0)
    (hfail : ∃ c : Component tail head T, (∑ v ∈ cell tail head T c, b v) ≠ 0) :
    ∃ c : Component tail head T, (∑ v ∈ cell tail head T c, b v) ≠ 0 ∧
      2*(cell tail head T c).card ≤ Fintype.card V := by
  obtain ⟨c,hc⟩ := hfail
  by_cases hsmall : 2*(cell tail head T c).card ≤ Fintype.card V
  · exact ⟨c,hc,hsmall⟩
  have he : ∃ d : Component tail head T, d ≠ c ∧ (∑ v ∈ cell tail head T d, b v) ≠ 0 := by
    by_contra hh
    push Not at hh
    have hsum : (∑ d : Component tail head T, ∑ v ∈ cell tail head T d, b v) =
        ∑ v ∈ cell tail head T c, b v := by
      apply sum_eq_single c
      · intro d _ hd; exact hh d hd
      · simp
    rw [sum_cells,hb] at hsum
    exact hc hsum.symm
  obtain ⟨d,hd,hfd⟩ := he
  refine ⟨d,hfd,?_⟩
  have hdis := cells_disjoint tail head T hd.symm
  have hcard := card_le_card (subset_univ (cell tail head T c ∪ cell tail head T d))
  rw [card_union_of_disjoint hdis,card_univ] at hcard
  omega

end

end WitnessedSeparation.Flows



namespace WitnessedSeparation.Grid

noncomputable section

open Classical Finset

variable {n : ℕ}

private theorem bound_of_boundary {r b : ℝ} (hr : 0 ≤ r) (_hb : 0 ≤ b)
    (h : boxConstant * r^((2:ℝ)/3) ≤ b) : r ≤ (b/boxConstant)^((3:ℝ)/2) := by
  have hu : r^((2:ℝ)/3) ≤ b/boxConstant := by
    apply (le_div_iff₀ boxConstant_pos).mpr
    simpa only [mul_comm] using h
  have hv := Real.rpow_le_rpow (Real.rpow_nonneg hr _) hu (by norm_num : (0:ℝ) ≤ 3/2)
  rw [←Real.rpow_mul hr] at hv
  norm_num at hv
  exact hv

theorem small_cell_bound (T : Finset (Edge n)) (c : Flows.Component tail head T)
    (hsmall : 2*(Flows.cell tail head T c).card ≤ (n+1)^3) :
    ((Flows.cell tail head T c).card:ℝ) ≤
      ((Flows.edgeBoundary tail head (Flows.cell tail head T c)).card / boxConstant)^((3:ℝ)/2) :=
  bound_of_boundary (by positivity) (by positivity)
    (box_boundary _ (Flows.cell_nonempty tail head T c) hsmall)

theorem partial_flow_small_obstruction (T : Finset (Edge n)) (σ : Edge n → Scalar)
    (hfail : ¬ ∃ k : Edge n → Scalar, Flows.incidence tail head k = 0 ∧
      ∀ e ∈ T, k e = σ e) :
    ∃ c : Flows.Component tail head T,
      (∑ v ∈ Flows.cell tail head T c,
        Flows.incidence tail head (fun e => if e ∈ T then σ e else 0) v) ≠ 0 ∧
      2*(Flows.cell tail head T c).card ≤ (n+1)^3 ∧
      ((Flows.cell tail head T c).card:ℝ) ≤
        (T.card/boxConstant)^((3:ℝ)/2) := by
  let z : Edge n → Scalar := fun e => if e ∈ T then σ e else 0
  have hf : ∃ v, (∑ w ∈ Flows.component tail head T v, Flows.incidence tail head z w) ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hfail ((Flows.partial_flow_iff tail head T σ).mpr hh)
  obtain ⟨v,hv⟩ := hf
  have hcell : Flows.cell tail head T (Flows.quotientMap tail head T v) =
      Flows.component tail head T v := by
    ext w
    rw [Flows.mem_cell,Flows.mem_component]
    exact ⟨fun h => Quotient.exact h.symm,fun h => (Quotient.sound h).symm⟩
  obtain ⟨c,hc,hs⟩ := Flows.small_failing_component tail head T (Flows.incidence tail head z)
    (Flows.sum_incidence tail head z) ⟨Flows.quotientMap tail head T v,by simpa only [hcell] using hv⟩
  have hcard : Fintype.card (Vertex n) = (n+1)^3 := by simp only [Vertex,Fintype.card_prod,Fintype.card_fin]; ring
  rw [hcard] at hs
  refine ⟨c,hc,hs,(small_cell_bound T c hs).trans ?_⟩
  apply Real.rpow_le_rpow (div_nonneg (Nat.cast_nonneg _) boxConstant_pos.le) _ (by norm_num)
  apply div_le_div_of_nonneg_right _ boxConstant_pos.le
  exact_mod_cast card_le_card (Flows.boundary_cell_subset tail head T c)

private theorem sum_rpow_le {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    ∑ i ∈ s, (f i)^((3:ℝ)/2) ≤ (∑ i ∈ s, f i)^((3:ℝ)/2) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [sum_insert ha,sum_insert ha]
    have hs : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf i (mem_insert_of_mem hi)
    calc
      f a ^ ((3:ℝ)/2) + ∑ i ∈ s, f i ^ ((3:ℝ)/2) ≤
          f a ^ ((3:ℝ)/2) + (∑ i ∈ s, f i) ^ ((3:ℝ)/2) := add_le_add (le_refl _) (ih hs)
      _ ≤ (f a + ∑ i ∈ s, f i) ^ ((3:ℝ)/2) :=
        Real.add_rpow_le_rpow_add (hf a (mem_insert_self _ _)) (sum_nonneg hs) (by norm_num)

theorem small_components_bound (T : Finset (Edge n)) (S : Finset (Flows.Component tail head T))
    (hs : ∀ c ∈ S, 2*(Flows.cell tail head T c).card ≤ (n+1)^3) :
    (∑ c ∈ S, ((Flows.cell tail head T c).card:ℝ)) ≤
      ((2*T.card:ℝ)/boxConstant)^((3:ℝ)/2) := by
  let b (c : Flows.Component tail head T) : ℝ :=
    (Flows.edgeBoundary tail head (Flows.cell tail head T c)).card / boxConstant
  have hn (c) : 0 ≤ b c := div_nonneg (Nat.cast_nonneg _) boxConstant_pos.le
  calc
    _ ≤ ∑ c ∈ S, (b c)^((3:ℝ)/2) := sum_le_sum (fun c hc => small_cell_bound T c (hs c hc))
    _ ≤ (∑ c ∈ S, b c)^((3:ℝ)/2) := sum_rpow_le S b (fun c _ => hn c)
    _ ≤ ((2*T.card:ℝ)/boxConstant)^((3:ℝ)/2) := by
      apply Real.rpow_le_rpow (sum_nonneg (fun c _ => hn c)) _ (by norm_num)
      dsimp [b]
      rw [←sum_div]
      apply div_le_div_of_nonneg_right _ boxConstant_pos.le
      calc
        _ ≤ ∑ c : Flows.Component tail head T,
            ((Flows.edgeBoundary tail head (Flows.cell tail head T c)).card:ℝ) :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => by positivity)
        _ ≤ 2*T.card := by exact_mod_cast Flows.sum_boundary_cells tail head T

theorem exists_giant (T : Finset (Edge n))
    (hnum : ((2*T.card:ℝ)/boxConstant)^((3:ℝ)/2) < ((n+1)^3:ℕ)) :
    ∃ c : Flows.Component tail head T, (n+1)^3 < 2*(Flows.cell tail head T c).card := by
  by_contra hh
  push Not at hh
  have h := small_components_bound T univ (fun c _ => hh c)
  rw [←Nat.cast_sum,Flows.sum_card_cells] at h
  have hc : Fintype.card (Vertex n) = (n+1)^3 := by simp only [Vertex,Fintype.card_prod,Fintype.card_fin]; ring
  rw [hc] at h
  exact (not_lt_of_ge h) hnum

end

end WitnessedSeparation.Grid



namespace WitnessedSeparation.Flows

noncomputable section

open Classical Finset

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

variable (tail head : E → V)

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem connected_mono {T U : Finset E} (hT : T ⊆ U) {v w : V}
    (h : (connected tail head U).r v w) : (connected tail head T).r v w := by
  induction h with
  | rel v w h =>
    obtain ⟨e,he,rfl,rfl⟩ := h
    exact edge_connected tail head T e (fun hh => he (hT hh))
  | refl v => exact .refl v
  | symm v w h ih => exact .symm _ _ ih
  | trans v w z h h' ih ih' => exact .trans _ _ _ ih ih'

omit [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem component_mono {T U : Finset E} (hT : T ⊆ U) (v : V) :
    component tail head U v ⊆ component tail head T v := by
  intro w hw
  exact (mem_component _ _ _ _ _).mpr (connected_mono tail head hT ((mem_component _ _ _ _ _).mp hw))

omit [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem giant_mono {T U : Finset E} (hT : T ⊆ U) {v : V} (h : IsGiant tail head U v) :
    IsGiant tail head T v := lt_of_lt_of_le h (Nat.mul_le_mul_left 2 (card_le_card (component_mono tail head hT v)))

omit [Fintype E] [DecidableEq E] in
theorem giants_connected {T : Finset E} {v w : V}
    (hv : IsGiant tail head T v) (hw : IsGiant tail head T w) : (connected tail head T).r v w := by
  by_contra hh
  have hd : Disjoint (component tail head T v) (component tail head T w) := by
    apply disjoint_left.mpr
    intro x hx hx'
    exact hh ((connected tail head T).trans ((mem_component _ _ _ _ _).mp hx)
      ((connected tail head T).symm ((mem_component _ _ _ _ _).mp hx')))
  have hk : (component tail head T v).card + (component tail head T w).card ≤ Fintype.card V := by
    rw [←card_union_of_disjoint hd]
    exact card_le_univ _
  dsimp [IsGiant] at hv hw
  omega

omit [Fintype E] [DecidableEq V] [DecidableEq E] in

theorem component_isolated {T : Finset E} (v : V)
    (h : ∀ e, tail e = v ∨ head e = v → e ∈ T) : component tail head T v = {v} := by
  have hh {x y : V} (hc : (connected tail head T).r x y) : x = v ↔ y = v := by
    induction hc with
    | rel x y hr =>
      obtain ⟨e,he,rfl,rfl⟩ := hr
      exact ⟨fun hv => False.elim (he (h e (Or.inl hv))),fun hv => False.elim (he (h e (Or.inr hv)))⟩
    | refl x => rfl
    | symm x y hc ih => exact ih.symm
    | trans x y z hc hc' ih ih' => exact ih.trans ih'
  ext w
  simp only [mem_component,mem_singleton]
  exact ⟨fun hw => (hh hw).mp rfl,fun hw => by subst w; exact (connected tail head T).refl _⟩

omit [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem giant_ne_isolated {T : Finset E} {w v : V} (hV : 2 ≤ Fintype.card V)
    (hw : IsGiant tail head T w) (h : ∀ e, tail e = v ∨ head e = v → e ∈ T) : w ≠ v := by
  intro he; subst w
  have hh := component_isolated tail head v h
  dsimp [IsGiant] at hw
  rw [hh,card_singleton] at hw
  omega

end

end WitnessedSeparation.Flows



namespace WitnessedSeparation.Grid

noncomputable section

open Classical Finset

variable {n : ℕ}

theorem grid_connected (v w : Vertex n) : (Flows.connected tail head ∅).r v w := by
  have hx (i j k : Fin (n+1)) : (Flows.connected tail head ∅).r (0,j,k) (i,j,k) := by
    induction i using Fin.induction with
    | zero => exact (Flows.connected tail head ∅).refl _
    | succ i ih =>
      exact (Flows.connected tail head ∅).trans ih (Flows.edge_connected tail head ∅ (ex i j k) (by simp))
  have hy (i j k : Fin (n+1)) : (Flows.connected tail head ∅).r (i,0,k) (i,j,k) := by
    induction j using Fin.induction with
    | zero => exact (Flows.connected tail head ∅).refl _
    | succ j ih =>
      exact (Flows.connected tail head ∅).trans ih (Flows.edge_connected tail head ∅ (ey i j k) (by simp))
  have hz (i j k : Fin (n+1)) : (Flows.connected tail head ∅).r (i,j,0) (i,j,k) := by
    induction k using Fin.induction with
    | zero => exact (Flows.connected tail head ∅).refl _
    | succ k ih =>
      exact (Flows.connected tail head ∅).trans ih (Flows.edge_connected tail head ∅ (ez i j k) (by simp))
  have h (v : Vertex n) : (Flows.connected tail head ∅).r (0,0,0) v :=
    (Flows.connected tail head ∅).trans (hx v.1 0 0)
      ((Flows.connected tail head ∅).trans (hy v.1 v.2.1 0) (hz v.1 v.2.1 v.2.2))
  exact (Flows.connected tail head ∅).trans ((Flows.connected tail head ∅).symm (h v)) (h w)

theorem grid_empty_component (v : Vertex n) : Flows.component tail head ∅ v = univ := by
  ext w; simp only [Flows.mem_component,mem_univ,iff_true]; exact grid_connected v w

theorem grid_empty_giant (v : Vertex n) : Flows.IsGiant tail head ∅ v := by
  dsimp [Flows.IsGiant]
  rw [grid_empty_component,card_univ]
  have hpos : 0 < Fintype.card (Vertex n) := Fintype.card_pos_iff.mpr ⟨(0,0,0)⟩
  omega

end





noncomputable section

open Classical Finset

variable {n M : ℕ} {b : Vertex n → Scalar}

theorem AtomShift.config_boundary {t : Edge n → Scalar} {v : Vertex n}
    {s : Configuration b v} {y : Atom b} (h : AtomShift t (.inr ⟨v,s⟩) y) :
    boundary t v = 0 := by
  cases h with
  | config v s h => simpa only [sub_self] using h

theorem quantitative_homogeneity_shift (hn : 1 ≤ n) {J : Type*} [Fintype J] [Nonempty (Atom b)]
    (names : J ↪ Fin M) (a a' : J → Atom b)
    (hw : (7*Fintype.card J:ℝ) + 7*((6*Fintype.card J:ℝ)/boxConstant)^((3:ℝ)/2)+1 ≤ M)
    (ht : Counting.tupleType (analysisStructure b) names a =
      Counting.tupleType (analysisStructure b) names a') :
    ∃ k : Edge n → Scalar, boundary k = 0 ∧ ∀ j, AtomShift k (a j) (a' j) := by
  let : Nonempty (Atom b) := ⟨.inr ⟨(0,0,0),someConfiguration hn b (0,0,0)⟩⟩
  have hp : 0 ≤ ((6*Fintype.card J:ℝ)/boxConstant)^((3:ℝ)/2) := Real.rpow_nonneg (div_nonneg (by positivity) boxConstant_pos.le) _
  have hw' : 7*Fintype.card J < M := by
    have hh : (7*Fintype.card J:ℝ)+1 ≤ M := by linarith
    have hh' : 7*Fintype.card J+1 ≤ M := by exact_mod_cast hh
    omega
  obtain ⟨σ,hσ⟩ := tuple_partial_shift names a a' hw' ht
  let T : Finset (Edge n) := touches univ a
  have hT : T.card ≤ 6*Fintype.card J := by simpa [T] using touches_card univ a
  suffices hs : ∃ k : Edge n → Scalar, Flows.incidence tail head k = 0 ∧ ∀ e ∈ T, k e = σ e by
    obtain ⟨k,hk,he⟩ := hs
    refine ⟨k,hk,fun j => (hσ j).congr ?_⟩
    intro e hej
    exact (he e (touch_subset_touches univ a (mem_univ j) hej)).symm
  by_contra hs
  obtain ⟨C,hbad,hsmall,hcard⟩ := partial_flow_small_obstruction T σ hs
  let U := Flows.cell tail head T C
  have hU : (U.card:ℝ) ≤ ((6*Fintype.card J:ℝ)/boxConstant)^((3:ℝ)/2) := by
    apply hcard.trans
    apply Real.rpow_le_rpow (div_nonneg (Nat.cast_nonneg _) boxConstant_pos.le) _ (by norm_num)
    apply div_le_div_of_nonneg_right _ boxConstant_pos.le
    exact_mod_cast hT
  let conf (v : U) : Atom b := .inr ⟨v.val,someConfiguration hn b v.val⟩
  have hwU : 7*Fintype.card (J ⊕ U) < M := by
    have hh : (7*(Fintype.card J+U.card):ℝ)+1 ≤ M := by linarith
    have hh' : 7*(Fintype.card J+U.card)+1 ≤ M := by exact_mod_cast hh
    simpa only [Fintype.card_sum,Fintype.card_coe] using (show 7*(Fintype.card J+U.card)<M by omega)
  have hcardU : Fintype.card (J ⊕ U) < M := by omega
  obtain ⟨conf',htU⟩ := Counting.tupleType_append (analysisStructure b) (analysisStructure b)
    names (namesBelow hcardU) a a' conf ht
  obtain ⟨d,hd⟩ := tuple_partial_shift (namesBelow hcardU) (Sum.elim a conf) (Sum.elim a' conf') hwU htU
  have hdT : ∀ e ∈ T, d e = σ e := by
    intro e he
    obtain ⟨j,hj,he⟩ := mem_biUnion.mp he
    exact (hd (.inl j)).unique_on_touch (hσ j) e he
  have hdU : ∀ v ∈ U, Flows.incidence tail head d v = 0 := by
    intro v hv
    exact (hd (.inr ⟨v,hv⟩)).config_boundary
  let z : Edge n → Scalar := fun e => if e ∈ T then σ e else 0
  have hd0 : ∀ e ∈ T, (d-z) e = 0 := by intro e he; simp [z,he,hdT e he]
  have hbal := Flows.sum_incidence_component tail head T (d-z) hd0 C.out
  have hsum : (∑ v ∈ U, Flows.incidence tail head d v) = 0 := sum_eq_zero hdU
  change (∑ v ∈ U, Flows.incidence tail head (d-z) v) = 0 at hbal
  simp only [map_sub,Pi.sub_apply,sum_sub_distrib,hsum,zero_sub,neg_eq_zero] at hbal
  exact hbad hbal

end





noncomputable section

open Classical

variable {n M : ℕ} {b : Vertex n → Scalar}

theorem central_atomShift (k : CentralGroup n) (x : Atom b) :
    AtomShift k.toAdd.val x (k • x) := by
  have hk (e : Edge n) : restrictGroup e (Support.H.central flowCycle k.toAdd) =
      Support.H.central (localCycle e) (k.toAdd.val e) := by
    apply Support.H.ext <;> rfl
  cases x with
  | inl x =>
    rcases x with ⟨e,s⟩
    change AtomShift k.toAdd.val (.inl ⟨e,s⟩)
      (.inl ⟨e,restrictGroup e (Support.H.central flowCycle k.toAdd)*s⟩)
    rw [hk]
    exact .edge e s
  | inr x =>
    rcases x with ⟨v,s⟩
    have hb : boundary k.toAdd.val v = b v-b v := by
      simp only [sub_self]
      exact congrFun k.toAdd.property v
    have hs : Support.H.central flowCycle k.toAdd • s = s.shift k.toAdd.val hb := by
      apply Configuration.ext
      intro e
      change restrictGroup e.val (Support.H.central flowCycle k.toAdd)*s.state e = _
      rw [hk]
      rfl
    change AtomShift k.toAdd.val (.inr ⟨v,s⟩) (.inr ⟨v,Support.H.central flowCycle k.toAdd • s⟩)
    rw [hs]
    exact .config v s hb

theorem quantitative_homogeneity (hn : 1 ≤ n) {J : Type*} [Fintype J] [Nonempty (Atom b)]
    (names : J ↪ Fin M) (a a' : J → Atom b)
    (hw : (7*Fintype.card J:ℝ) + 7*((6*Fintype.card J:ℝ)/boxConstant)^((3:ℝ)/2)+1 ≤ M)
    (ht : Counting.tupleType (analysisStructure b) names a =
      Counting.tupleType (analysisStructure b) names a') :
    ∃ k : CentralGroup n, ∀ j, k • a j = a' j := by
  obtain ⟨k,hk,ha⟩ := quantitative_homogeneity_shift hn names a a' hw ht
  let g : CentralGroup n := Multiplicative.ofAdd ⟨k,hk⟩
  exact ⟨g,fun j => (central_atomShift g (a j)).functional (ha j)⟩

end

end WitnessedSeparation.Grid



namespace WitnessedSeparation.Counting.Formula

noncomputable section

open Classical Finset

variable {R I A B : Type*} [DecidableEq I]

theorem eval_of_partialBijectionSystem (S : Structure R A) (T : Structure R B)
    (E : Finset I → (I → A) → (I → B) → Prop)
    (heq : ∀ names v w, E names v w → ∀ i ∈ names, ∀ j ∈ names, (v i = v j ↔ w i = w j))
    (hrel : ∀ names v w, E names v w → ∀ r i, i ∈ names → ∀ j, j ∈ names →
      (S.rel r (v i) (v j) ↔ T.rel r (w i) (w j)))
    (hext : ∀ names v w, E names v w → ∀ i, ∃ e : A ≃ B,
      ∀ a, E (insert i (names.erase i)) (Function.update v i a) (Function.update w i (e a)))
    (φ : Formula R I) : ∀ names v w, E names v w → φ.free ⊆ names →
      (φ.eval S v ↔ φ.eval T w) := by
  induction φ with
  | falsum => intros; rfl
  | equal i j =>
    intro names v w h hf
    exact heq names v w h i (hf (by simp [free])) j (hf (by simp [free]))
  | relation r i j =>
    intro names v w h hf
    exact hrel names v w h r i (hf (by simp [free])) j (hf (by simp [free]))
  | neg φ ih => intro names v w h hf; exact not_congr (ih names v w h hf)
  | and φ ψ ih ih' =>
    intro names v w h hf
    exact and_congr (ih names v w h (subset_union_left.trans hf))
      (ih' names v w h (subset_union_right.trans hf))
  | ex i φ ih =>
    intro names v w h hf
    obtain ⟨e,he⟩ := hext names v w h i
    have hfree : φ.free ⊆ insert i (names.erase i) := by
      intro j hj
      by_cases hji : j = i
      · simp [hji]
      · exact mem_insert_of_mem (mem_erase.mpr ⟨hji,hf (mem_erase.mpr ⟨hji,hj⟩)⟩)
    change (∃ a, φ.eval S (Function.update v i a)) ↔ _
    constructor
    · rintro ⟨a,ha⟩; exact ⟨e a,(ih _ _ _ (he a) hfree).mp ha⟩
    · rintro ⟨b,hb⟩; obtain ⟨a,rfl⟩ := e.surjective b
      exact ⟨a,(ih _ _ _ (he a) hfree).mpr hb⟩
  | exact i n φ ih =>
    intro names v w h hf
    obtain ⟨e,he⟩ := hext names v w h i
    have hfree : φ.free ⊆ insert i (names.erase i) := by
      intro j hj
      by_cases hji : j = i
      · simp [hji]
      · exact mem_insert_of_mem (mem_erase.mpr ⟨hji,hf (mem_erase.mpr ⟨hji,hj⟩)⟩)
    let f : {a : A // φ.eval S (Function.update v i a)} ≃
        {b : B // φ.eval T (Function.update w i b)} :=
      e.subtypeEquiv (fun a => ih _ _ _ (he a) hfree)
    exact ⟨fun ⟨g⟩ => ⟨f.symm.trans g⟩,fun ⟨g⟩ => ⟨f.trans g⟩⟩

end

end WitnessedSeparation.Counting.Formula

end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_SupportedForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace WitnessedSeparation.Grid

noncomputable section

open Classical Finset

variable {n M : ℕ} {b b' : Vertex n → Scalar}

theorem boundary_eq_incidence : (boundary : (Edge n → Scalar) →ₗ[Scalar] (Vertex n → Scalar)) =
    Flows.incidence tail head := rfl

theorem giant_exists_of_bound (hbound : GiantBound n M) (T : Finset (Edge n)) (hT : T.card ≤ 6*M) :
    ∃ v, Flows.IsGiant tail head T v := by
  have hnum : ((2*T.card:ℝ)/boxConstant)^((3:ℝ)/2) < ((n+1)^3:ℕ) := by
    apply lt_of_le_of_lt _ hbound
    apply Real.rpow_le_rpow (div_nonneg (by positivity) boxConstant_pos.le) _ (by norm_num)
    apply div_le_div_of_nonneg_right _ boxConstant_pos.le
    have hh : (T.card:ℝ) ≤ 6*M := by exact_mod_cast hT
    linarith
  obtain ⟨c,hc⟩ := exists_giant T hnum
  refine ⟨c.out,?_⟩
  change Fintype.card (Vertex n) < 2*(Flows.cell tail head T c).card
  have hcard : Fintype.card (Vertex n) = (n+1)^3 := by
    simp only [Vertex,Fintype.card_prod,Fintype.card_fin]; ring
  simpa only [hcard] using hc

theorem defect_transport (hbound : GiantBound n M) (T U : Finset (Edge n)) (hTU : T ⊆ U)
    (hU : U.card ≤ 6*M) (t : Edge n → Scalar) (w : Vertex n)
    (hw : Flows.IsGiant tail head T w) (ht : boundary t = b'-b-Pi.single w 1) :
    ∃ t' : Edge n → Scalar, ∃ w' : Vertex n,
      Flows.IsGiant tail head U w' ∧ boundary t' = b'-b-Pi.single w' 1 ∧ ∀ e ∈ T, t' e = t e := by
  obtain ⟨w',hw'⟩ := giant_exists_of_bound hbound U hU
  have hc := Flows.giants_connected tail head (Flows.giant_mono tail head hTU hw') hw
  obtain ⟨p,hp,hd⟩ := Flows.path_flow tail head T hc
  refine ⟨t+p,w',hw',?_,?_⟩
  · rw [map_add,ht,boundary_eq_incidence,hd]
    abel
  · intro e he; simp [hp e he]

theorem CompatibleAssignment.mono {I : Type*} [DecidableEq I] {names small : Finset I}
    (hs : small ⊆ names) {a : I → Atom b} {a' : I → Atom b'}
    (h : CompatibleAssignment names a a') : CompatibleAssignment small a a' := by
  obtain ⟨t,w,hw,ht,ha⟩ := h
  exact ⟨t,w,Flows.giant_mono tail head (touches_mono hs a) hw,ht,fun i hi => ha i (hs hi)⟩

theorem CompatibleAssignment.extend (hn : 1 ≤ n) (hbound : GiantBound n M)
    (names : Finset (Fin M)) (a : Fin M → Atom b) (a' : Fin M → Atom b')
    (h : CompatibleAssignment names a a') (i : Fin M) :
    ∃ e : Atom b ≃ Atom b', ∀ x,
      CompatibleAssignment (insert i (names.erase i)) (Function.update a i x) (Function.update a' i (e x)) := by
  obtain ⟨t,w,hw,ht,ha⟩ := h.mono (erase_subset i names)
  let T := touches (names.erase i) a
  have hcard : (names.erase i).card + 1 ≤ M := by
    have hsub : names.erase i ⊆ (univ : Finset (Fin M)).erase i := erase_subset_erase i (subset_univ _)
    have hh := card_le_card hsub
    have hpos := i.isLt
    rw [card_erase_of_mem (mem_univ _),card_univ,Fintype.card_fin] at hh
    omega
  have hj (J : Block n) : (T ∪ blockEdges J).card ≤ 6*M := by
    calc
      _ ≤ T.card + (blockEdges J).card := card_union_le _ _
      _ ≤ 6*(names.erase i).card + 6 := Nat.add_le_add (touches_card _ _) (blockEdges_card _)
      _ ≤ 6*M := by omega
  have hmove (J : Block n) := defect_transport hbound T (T ∪ blockEdges J)
    subset_union_left (hj J) t w hw ht
  choose tj wj hjg hjd hjs using hmove
  have hV : 2 ≤ Fintype.card (Vertex n) := by
    have hc : Fintype.card (Vertex n) = (n+1)^3 := by
      simp only [Vertex,Fintype.card_prod,Fintype.card_fin]; ring
    rw [hc]
    have hh : 2^3 ≤ (n+1)^3 := Nat.pow_le_pow_left (by omega) 3
    omega
  have hv (v : Vertex n) : boundary (tj (.inr v)) v = b' v-b v := by
    have hwv : wj (.inr v) ≠ v := Flows.giant_ne_isolated tail head hV (hjg (.inr v)) (by
      intro e he
      exact mem_union_right _ (by simpa [blockEdges,incident,or_comm] using he))
    have hh := congrFun (hjd (.inr v)) v
    simpa [Pi.single_apply,Ne.symm hwv] using hh
  let e := blockShiftEquiv (fun e => tj (.inl e)) (fun v => tj (.inr v)) hv
  refine ⟨e,fun x => ?_⟩
  let J := atomBlock x
  refine ⟨tj J,wj J,?_,hjd J,?_⟩
  · rw [touches_insert_update]
    exact hjg J
  · intro j hj'
    rcases mem_insert.mp hj' with rfl | hj'
    · simp only [Function.update_self]
      cases x with
      | inl x => rcases x with ⟨f,s⟩; exact AtomShift.edge f s
      | inr x => rcases x with ⟨v,s⟩; exact AtomShift.config v s (hv v)
    · have hji := (mem_erase.mp hj').1
      simp only [Function.update_of_ne hji]
      exact (ha j hj').congr (fun f hf => (hjs J f (touch_subset_touches _ _ hj' hf)).symm)

theorem base_equivalence_numeric (hn : 1 ≤ n) (hbound : GiantBound n M) (vstar : Vertex n)
    (φ : Counting.Formula AnalysisSymbol (Fin M)) (hφ : φ.free = ∅)
    (a : Fin M → Atom (0 : Vertex n → Scalar))
    (a' : Fin M → Atom (Pi.single vstar 1)) :
    φ.eval (analysisStructure (0 : Vertex n → Scalar)) a ↔
      φ.eval (analysisStructure (Pi.single vstar 1)) a' := by
  have heq : ∀ (names : Finset (Fin M)) (v : Fin M → Atom (0 : Vertex n → Scalar))
      (w : Fin M → Atom (Pi.single vstar 1)), CompatibleAssignment names v w → ∀ i ∈ names, ∀ j ∈ names,
      (v i = v j ↔ w i = w j) := by
    intro names v w ⟨t,x,hg,hb,ha⟩ i hi j hj
    exact (ha i hi).equal_iff (ha j hj)
  have hrel : ∀ (names : Finset (Fin M)) (v : Fin M → Atom (0 : Vertex n → Scalar))
      (w : Fin M → Atom (Pi.single vstar 1)), CompatibleAssignment names v w → ∀ r i, i ∈ names → ∀ j, j ∈ names →
      ((analysisStructure (0 : Vertex n → Scalar)).rel r (v i) (v j) ↔
      (analysisStructure (Pi.single vstar 1)).rel r (w i) (w j)) := by
    intro names v w ⟨t,x,hg,hb,ha⟩ r i hi j hj
    exact (ha i hi).analysisRelation (ha j hj) r
  apply Counting.Formula.eval_of_partialBijectionSystem _ _ CompatibleAssignment heq hrel
    (fun names v w hh i => CompatibleAssignment.extend hn hbound names v w hh i) φ ∅ a a' _ (by simp [hφ])
  refine ⟨0,vstar,?_,by simp,by simp⟩
  simpa [touches] using grid_empty_giant vstar

end

end WitnessedSeparation.Grid



namespace WitnessedSeparation.Forms

noncomputable section

open Classical

open Counting Hereditary

variable {R I J A B : Type*}

theorem swap_type [Fintype J] [DecidableEq I] [Nonempty A] [Nonempty B]
    (S : Structure R A) (T : Structure R B) (e : J ⊕ J ↪ I)
    (a b : J → A) (a' b' : J → B)
    (h : tupleType S e (Sum.elim a b) = tupleType T e (Sum.elim a' b')) :
    tupleType S e (Sum.elim b a) = tupleType T e (Sum.elim b' a') := by
  have ht := tupleType_project S T e e (Equiv.sumComm J J).toEmbedding _ _ h
  have h1 : Sum.elim a b ∘ (Equiv.sumComm J J).toEmbedding = Sum.elim b a := by
    funext j; cases j <;> rfl
  have h2 : Sum.elim a' b' ∘ (Equiv.sumComm J J).toEmbedding = Sum.elim b' a' := by
    funext j; cases j <;> rfl
  simpa only [h1,h2] using ht

section AtomicTransfer

variable [Fintype I] [Fintype J] [DecidableEq I]

variable [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]

variable (S : Structure R A) (T : Structure R B)

variable (e2 : J ⊕ J ↪ I) (e3 : (J ⊕ J) ⊕ J ↪ I)

variable (e4 : ((J ⊕ J) ⊕ J) ⊕ J ↪ I)

open Form

include e3 e4

private theorem set_subset_transfer
    (n k : ℕ) (child : Fin n → Form J (Set (Formula R I)))
    (other : Fin k → Form J (Set (Formula R I)))
    (label : Fin n → Set (Formula R I)) (lab : Fin k → Set (Formula R I))
    (hc : ∀ i j (c d : J → A) (c' d' : J → B),
      tupleType S e2 (Sum.elim c d) = tupleType T e2 (Sum.elim c' d') →
      (value S e2 (child i) c = value S e2 (other j) d ↔
        value T e2 (child i) c' = value T e2 (other j) d'))
    (a b : J → A) (a' b' : J → B)
    (ht : tupleType S e2 (Sum.elim a b) = tupleType T e2 (Sum.elim a' b'))
    (hsub : ∀ x, x ∈ value S e2 (.set n child label) a →
      x ∈ value S e2 (.set k other lab) b) :
    ∀ x, x ∈ value T e2 (.set n child label) a' →
      x ∈ value T e2 (.set k other lab) b' := by
  intro x hx
  obtain ⟨i,c',hl,rfl⟩ := (mem_value_set T e2 n child label a' x).mp hx
  obtain ⟨c,h3⟩ := tupleType_append T S e2 e3 (Sum.elim a' b') (Sum.elim a b) c' ht.symm
  have hca := tupleType_project T S e3 e2 cross31 _ _ h3
  simp only [elim_comp_cross31] at hca
  have hmem : value S e2 (child i) c ∈ value S e2 (.set n child label) a :=
    (mem_value_set S e2 n child label a _).mpr ⟨i,c,hca.symm.trans hl,rfl⟩
  obtain ⟨j,d,hlab,heq⟩ := (mem_value_set S e2 k other lab b _).mp (hsub _ hmem)
  obtain ⟨d',h4⟩ := tupleType_append S T e3 e4 (Sum.elim (Sum.elim a b) c)
    (Sum.elim (Sum.elim a' b') c') d h3.symm
  have hdb := tupleType_project S T e4 e2 cross42 _ _ h4
  have hcd := tupleType_project S T e4 e2 cross34 _ _ h4
  simp only [elim_comp_cross42] at hdb
  simp only [elim_comp_cross34] at hcd
  exact (mem_value_set T e2 k other lab b' _).mpr
    ⟨j,d',hdb.symm.trans hlab,((hc i j c d c' d' hcd).mp heq.symm).symm⟩

private theorem set_eq_forward
    (n k : ℕ) (child : Fin n → Form J (Set (Formula R I)))
    (other : Fin k → Form J (Set (Formula R I)))
    (label : Fin n → Set (Formula R I)) (lab : Fin k → Set (Formula R I))
    (hc : ∀ i j (c d : J → A) (c' d' : J → B),
      tupleType S e2 (Sum.elim c d) = tupleType T e2 (Sum.elim c' d') →
      (value S e2 (child i) c = value S e2 (other j) d ↔
        value T e2 (child i) c' = value T e2 (other j) d'))
    (a b : J → A) (a' b' : J → B)
    (ht : tupleType S e2 (Sum.elim a b) = tupleType T e2 (Sum.elim a' b'))
    (h : value S e2 (.set n child label) a = value S e2 (.set k other lab) b) :
    value T e2 (.set n child label) a' = value T e2 (.set k other lab) b' := by
  apply Hereditary.ext_sets (by simp) (by simp)
  intro x
  constructor
  · exact set_subset_transfer S T e2 e3 e4 n k child other label lab hc a b a' b' ht
      (fun z hz => by rw [←h]; exact hz) x
  · apply set_subset_transfer S T e2 e3 e4 k n other child lab label
      (fun j i c d c' d' ht' => ?_) b a b' a' (swap_type S T e2 a b a' b' ht)
      (fun z hz => by rw [h]; exact hz) x
    have hh := hc i j d c d' c' (swap_type S T e2 c d c' d' ht')
    exact ⟨fun he => (hh.mp he.symm).symm,fun he => (hh.mpr he.symm).symm⟩

theorem equality_transfer (φ ψ : Form J (Set (Formula R I)))
    (a b : J → A) (a' b' : J → B)
    (ht : tupleType S e2 (Sum.elim a b) = tupleType T e2 (Sum.elim a' b')) :
    value S e2 φ a = value S e2 ψ b ↔ value T e2 φ a' = value T e2 ψ b' := by
  induction φ generalizing ψ a b a' b' with
  | atom i =>
    cases ψ with
    | atom j =>
      have he := (typeOf_eq_iff S T (tupleNames e2) _ _).mp ht
        (.equal (e2 (.inl i)) (e2 (.inr j))) (by
          intro p hp
          simp only [Formula.free,Finset.mem_insert,Finset.mem_singleton] at hp
          rcases hp with rfl | rfl <;> exact (mem_tupleNames _ _).mpr ⟨_,rfl⟩)
      simpa only [Formula.eval,tupleAssignment_apply,Sum.elim_inl,Sum.elim_inr,
        value_atom,Hereditary.atom_injective.eq_iff] using he
    | set k other lab =>
      have hfalseA : value S e2 (.atom i) a ≠ value S e2 (.set k other lab) b := by
        intro h; have hh := congrArg isSet h; simp at hh
      have hfalseB : value T e2 (.atom i) a' ≠ value T e2 (.set k other lab) b' := by
        intro h; have hh := congrArg isSet h; simp at hh
      exact iff_of_false hfalseA hfalseB
  | set n child label ih =>
    cases ψ with
    | atom j =>
      have hfalseA : value S e2 (.set n child label) a ≠ value S e2 (.atom j) b := by
        intro h; have hh := congrArg isSet h; simp at hh
      have hfalseB : value T e2 (.set n child label) a' ≠ value T e2 (.atom j) b' := by
        intro h; have hh := congrArg isSet h; simp at hh
      exact iff_of_false hfalseA hfalseB
    | set k other lab =>
      constructor
      · exact set_eq_forward S T e2 e3 e4 n k child other label lab
          (fun i j c d c' d' ht' => ih i (other j) c d c' d' ht') a b a' b' ht
      · exact set_eq_forward T S e2 e3 e4 n k child other label lab
          (fun i j c' d' c d ht' => (ih i (other j) c d c' d' ht'.symm).symm)
          a' b' a b ht.symm

private theorem membership_forward (φ : Form J (Set (Formula R I)))
    (k : ℕ) (other : Fin k → Form J (Set (Formula R I)))
    (lab : Fin k → Set (Formula R I))
    (a b : J → A) (a' b' : J → B)
    (ht : tupleType S e2 (Sum.elim a b) = tupleType T e2 (Sum.elim a' b'))
    (hm : value S e2 φ a ∈ value S e2 (.set k other lab) b) :
    value T e2 φ a' ∈ value T e2 (.set k other lab) b' := by
  obtain ⟨i,c,hl,heq⟩ := (mem_value_set S e2 k other lab b _).mp hm
  obtain ⟨c',h3⟩ := tupleType_append S T e2 e3 (Sum.elim b a) (Sum.elim b' a') c
    (swap_type S T e2 a b a' b' ht)
  have hcb := tupleType_project S T e3 e2 cross31 _ _ h3
  simp only [elim_comp_cross31] at hcb
  let u : J ⊕ J ↪ (J ⊕ J) ⊕ J :=
    cross31.trans (Function.Embedding.sumMap (Equiv.sumComm J J).toEmbedding
      (Function.Embedding.refl J))
  have hca := tupleType_project S T e3 e2 u _ _ h3
  have hueq (a b c : J → A) : Sum.elim (Sum.elim b a) c ∘ u = Sum.elim c a := by
    funext j; cases j <;> rfl
  have hueq' (a b c : J → B) : Sum.elim (Sum.elim b a) c ∘ u = Sum.elim c a := by
    funext j; cases j <;> rfl
  rw [hueq,hueq'] at hca
  exact (mem_value_set T e2 k other lab b' _).mpr ⟨i,c',hcb.symm.trans hl,
    (equality_transfer S T e2 e3 e4 (other i) φ c a c' a' hca).mp heq⟩

theorem membership_transfer (φ ψ : Form J (Set (Formula R I)))
    (a b : J → A) (a' b' : J → B)
    (ht : tupleType S e2 (Sum.elim a b) = tupleType T e2 (Sum.elim a' b')) :
    value S e2 φ a ∈ value S e2 ψ b ↔ value T e2 φ a' ∈ value T e2 ψ b' := by
  cases ψ with
  | atom j => simp
  | set k other lab =>
    exact ⟨membership_forward S T e2 e3 e4 φ k other lab a b a' b' ht,
      membership_forward T S e2 e3 e4 φ k other lab a' b' a b ht.symm⟩

end AtomicTransfer


variable {G : Type*} [Group G] [MulAction G A]

variable [Fintype I] [DecidableEq I] [Fintype A] [Nonempty A] {s : ℕ}

variable (S : Structure R A) (e2 : Fin s ⊕ Fin s ↪ I)

variable (hAut : ∀ (g : G) r a b, S.rel r (g • a) (g • b) ↔ S.rel r a b)

open Form

omit [Fintype A] [Nonempty A] in
private theorem hereditary_mem {x y : HF A}
    (hx : HereditarilySupported (G := G) s x) (hy : y ∈ x) :
    HereditarilySupported (G := G) s y := by
  intro z hz
  exact hx z (hz.trans (Relation.ReflTransGen.single hy))

omit [Fintype A] [Nonempty A] in
private theorem smul_mem (g : G) {x y : HF A} (h : y ∈ x) : g • y ∈ g • x := by
  change Hereditary.map (fun a => g • a) y ∈
    elements (Hereditary.map (fun a => g • a) x)
  let := Hereditary.instDecidableEqHF (A := A)
  rw [elements_map]
  exact Finset.mem_image.mpr ⟨y,h,rfl⟩

include hAut in
omit [Fintype I] in


theorem representation (hs : 0 < s)
    (hHom : ∀ p q : Fin s ⊕ Fin s → A,
      tupleType S e2 p = tupleType S e2 q → ∃ g : G, ∀ i, g • p i = q i)
    (x : HF A) (hx : HereditarilySupported (G := G) s x) :
    ∃ φ : Form (Fin s) (Set (Formula R I)), ∃ a : Fin s → A, value S e2 φ a = x := by
  induction x using mem_wellFounded.induction with
  | h x ih =>
    rcases atom_or_set x with ⟨b,rfl⟩ | hxset
    · exact ⟨.atom ⟨0,hs⟩,fun _ => b,rfl⟩
    · obtain ⟨a,ha⟩ := hx x Relation.ReflTransGen.refl
      have hr : ∀ y : {y // y ∈ elements x},
          ∃ φ : Form (Fin s) (Set (Formula R I)), ∃ b : Fin s → A,
            value S e2 φ b = y.1 := by
        intro y
        exact ih y.1 y.2 (hereditary_mem hx y.2)
      choose form mol hvalue using hr
      let n := Fintype.card {y // y ∈ elements x}
      let en : Fin n ≃ {y // y ∈ elements x} := (Fintype.equivFin _).symm
      let child : Fin n → Form (Fin s) (Set (Formula R I)) := fun i => form (en i)
      let β : Fin n → Fin s → A := fun i => mol (en i)
      let label : Fin n → Set (Formula R I) := fun i => tupleType S e2 (Sum.elim (β i) a)
      refine ⟨.set n child label,a,?_⟩
      apply Hereditary.ext_sets (by simp) (by rw [hxset]; rfl)
      intro y
      constructor
      · intro hy
        obtain ⟨i,b,ht,rfl⟩ := (mem_value_set S e2 n child label a y).mp hy
        obtain ⟨g,hg⟩ := hHom (Sum.elim (β i) a) (Sum.elim b a) ht.symm
        have hga : ∀ j, g • a j = a j := fun j => hg (.inr j)
        have hgb : (fun j => g • β i j) = b := funext (fun j => hg (.inl j))
        have hyx : (en i).1 ∈ x := (en i).2
        have hmap := smul_mem g hyx
        rw [ha g hga] at hmap
        have hv : value S e2 (child i) b = g • (en i).1 := by
          rw [←hgb,←value_smul S e2 hAut]
          exact congrArg (fun z : HF A => g • z) (hvalue (en i))
        rw [hv]
        exact hmap
      · intro hy
        let y' : {y // y ∈ elements x} := ⟨y,hy⟩
        let i := en.symm y'
        apply (mem_value_set S e2 n child label a y).mpr
        refine ⟨i,β i,rfl,?_⟩
        have hv := hvalue (en i)
        simpa only [child,β,i,Equiv.apply_symm_apply] using hv


end

end WitnessedSeparation.Forms



namespace WitnessedSeparation.Counting

noncomputable section

open Classical

variable {R I J A B : Type*} [DecidableEq I]


variable [Fintype I] [Fintype J] [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]

theorem tupleType_append_one_bijection (S : Structure R A) (T : Structure R B)
    (e : J ↪ I) (E : J ⊕ Unit ↪ I) (a : J → A) (b : J → B)
    (ht : tupleType S e a = tupleType T e b) :
    ∃ f : A ≃ B, ∀ x, tupleType S E (Sum.elim a (fun _ => x)) =
      tupleType T E (Sum.elim b (fun _ => f x)) := by
  let ep := Function.Embedding.inl.trans E
  let i := E (Sum.inr ())
  have hp := tupleType_project S T e ep (Function.Embedding.refl J) a b ht
  change tupleType S ep a = tupleType T ep b at hp
  have hi : i ∉ tupleNames ep := by
    rintro hh
    obtain ⟨j,hj⟩ := (mem_tupleNames ep i).mp hh
    have hh := E.injective hj
    cases hh
  have hn : insert i (tupleNames ep) = tupleNames E := by
    ext p
    simp only [Finset.mem_insert,mem_tupleNames]
    constructor
    · rintro (rfl|⟨j,rfl⟩)
      · exact ⟨Sum.inr (),rfl⟩
      · exact ⟨Sum.inl j,rfl⟩
    · rintro ⟨j,rfl⟩
      rcases j with j|u
      · exact Or.inr ⟨j,rfl⟩
      · cases u; exact Or.inl rfl
  have ha (x : A) : tupleType S E (Sum.elim a (fun _ => x)) =
      typeOf S (tupleNames E) (Function.update (tupleAssignment ep a) i x) := by
    apply tupleType_assignment
    intro j
    rcases j with j|u
    · have hne : E (Sum.inl j) ≠ i := by
        intro h; have hh := E.injective h; cases hh
      rw [Function.update_of_ne hne]
      exact tupleAssignment_apply ep a j
    · cases u; simp [i]
  have hb (x : B) : tupleType T E (Sum.elim b (fun _ => x)) =
      typeOf T (tupleNames E) (Function.update (tupleAssignment ep b) i x) := by
    apply tupleType_assignment
    intro j
    rcases j with j|u
    · have hne : E (Sum.inl j) ≠ i := by
        intro h; have hh := E.injective h; cases hh
      rw [Function.update_of_ne hne]
      exact tupleAssignment_apply ep b j
    · cases u; simp [i]
  obtain ⟨f,hf⟩ := extension_bijection S T (tupleNames ep) i hi
    (tupleAssignment ep a) (tupleAssignment ep b) hp
  refine ⟨f,fun x => ?_⟩
  rw [ha,hb]
  simpa only [hn] using hf x

theorem tupleType_append_fin_bijection (S : Structure R A) (T : Structure R B)
    (e : J ↪ I) (n : ℕ) (E : J ⊕ Fin n ↪ I) (a : J → A) (b : J → B)
    (ht : tupleType S e a = tupleType T e b) :
    ∃ f : (Fin n → A) ≃ (Fin n → B), ∀ c,
      tupleType S E (Sum.elim a c) = tupleType T E (Sum.elim b (f c)) := by
  induction n with
  | zero =>
    let f : (Fin 0 → A) ≃ (Fin 0 → B) :=
      ⟨fun _ => Fin.elim0,fun _ => Fin.elim0,
        fun _ => Subsingleton.elim _ _,fun _ => Subsingleton.elim _ _⟩
    refine ⟨f,fun c => ?_⟩
    let u : J ⊕ Fin 0 ↪ J :=
      ⟨Sum.elim id Fin.elim0,by
        intro x y h
        rcases x with x|x
        · rcases y with y|y
          · exact congrArg Sum.inl h
          · exact Fin.elim0 y
        · exact Fin.elim0 x⟩
    have h := tupleType_project S T e E u a b ht
    have ha : a ∘ u = Sum.elim a c := by
      funext j; rcases j with j|i
      · rfl
      · exact Fin.elim0 i
    have hb : b ∘ u = Sum.elim b (f c) := by
      funext j; rcases j with j|i
      · rfl
      · exact Fin.elim0 i
    simpa only [ha,hb] using h
  | succ n ih =>
    let pre : J ⊕ Fin n ↪ J ⊕ Fin (n+1) :=
      Function.Embedding.sumMap (Function.Embedding.refl J) Fin.castSuccEmb
    let ep := pre.trans E
    obtain ⟨f,hf⟩ := ih ep
    let E1 := (appendPosition J n).toEmbedding.trans E
    have h1 (c : Fin n → A) : ∃ g : A ≃ B, ∀ x,
        tupleType S E1 (Sum.elim (Sum.elim a c) (fun _ => x)) =
        tupleType T E1 (Sum.elim (Sum.elim b (f c)) (fun _ => g x)) :=
      tupleType_append_one_bijection S T ep E1 _ _ (hf c)
    choose g hg using h1
    let F := (snocEquiv (A:=A) n).trans
      ((triangular f g).trans (snocEquiv (A:=B) n).symm)
    refine ⟨F,fun c => ?_⟩
    have hh := tupleType_project S T E1 E (appendPosition J n).symm.toEmbedding
      _ _ (hg (fun i => c i.castSucc) (c (Fin.last n)))
    have ha : (Sum.elim (Sum.elim a (fun i => c i.castSucc))
        (fun _ => c (Fin.last n))) ∘ (appendPosition J n).symm = Sum.elim a c := by
      funext j
      rcases j with j|i
      · rfl
      · induction i using Fin.lastCases <;> simp [appendPosition]
    have hb : (Sum.elim (Sum.elim b (f (fun i => c i.castSucc)))
        (fun _ => g (fun i => c i.castSucc) (c (Fin.last n)))) ∘
        (appendPosition J n).symm = Sum.elim b (F c) := by
      funext j
      rcases j with j|i
      · rfl
      · induction i using Fin.lastCases <;>
          simp [appendPosition,F,snocEquiv,triangular,snocTuple]
    simpa only [Equiv.coe_toEmbedding,ha,hb] using hh

theorem tupleType_append_bijection {D : Type*} [Fintype D]
    (S : Structure R A) (T : Structure R B)
    (e : J ↪ I) (E : J ⊕ D ↪ I) (a : J → A) (b : J → B)
    (ht : tupleType S e a = tupleType T e b) :
    ∃ f : (D → A) ≃ (D → B), ∀ c,
      tupleType S E (Sum.elim a c) = tupleType T E (Sum.elim b (f c)) := by
  let en := Fintype.equivFin D
  let E' := (Equiv.sumCongr (Equiv.refl J) en.symm).toEmbedding.trans E
  obtain ⟨f,hf⟩ := tupleType_append_fin_bijection S T e (Fintype.card D) E' a b ht
  let F := (Equiv.arrowCongr en (Equiv.refl A)).trans
    (f.trans (Equiv.arrowCongr en.symm (Equiv.refl B)))
  refine ⟨F,fun c => ?_⟩
  have hh := tupleType_project S T E' E
    (Equiv.sumCongr (Equiv.refl J) en).toEmbedding _ _ (hf (c ∘ en.symm))
  have ha : (Sum.elim a (c ∘ en.symm)) ∘ (Equiv.sumCongr (Equiv.refl J) en) =
      Sum.elim a c := by
    funext j; rcases j with j|j <;> simp
  have hb : (Sum.elim b (f (c ∘ en.symm))) ∘ (Equiv.sumCongr (Equiv.refl J) en) =
      Sum.elim b (F c) := by
    funext j; rcases j with j|j <;> rfl
  simpa only [Equiv.coe_toEmbedding,ha,hb] using hh

theorem tupleType_extension_equiv {D : Type*} [Fintype D]
    (S : Structure R A) (T : Structure R B)
    (e : J ↪ I) (E : J ⊕ D ↪ I) (a : J → A) (b : J → B)
    (ht : tupleType S e a = tupleType T e b) (τ : Set (Formula R I)) :
    Nonempty ({c : D → A // tupleType S E (Sum.elim a c) = τ} ≃
      {d : D → B // tupleType T E (Sum.elim b d) = τ}) := by
  obtain ⟨f,hf⟩ := tupleType_append_bijection S T e E a b ht
  exact ⟨f.subtypeEquiv (fun c => by rw [hf c])⟩


end

end WitnessedSeparation.Counting



namespace WitnessedSeparation.Forms

noncomputable section

open Classical Counting Hereditary

open scoped BigOperators

private theorem card_eq_mul_fiber {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y) (y₀ : Y)
    (h : ∀ y, Fintype.card {x // f x = y} = Fintype.card {x // f x = y₀}) :
    Fintype.card X = Fintype.card Y * Fintype.card {x // f x = y₀} := by
  calc
    Fintype.card X = Fintype.card (Σ y, {x // f x = y}) :=
      Fintype.card_congr (Equiv.sigmaFiberEquiv f).symm
    _ = ∑ y, Fintype.card {x // f x = y} := Fintype.card_sigma
    _ = _ := by simp only [h,Finset.sum_const,Finset.card_univ,smul_eq_mul]

private theorem range_card_mul_fiber {X Y : Type*} [Fintype X]
    (f : X → Y) (x₀ : X)
    (h : ∀ x, Nat.card {z // f z = f x} = Nat.card {z // f z = f x₀}) :
    Fintype.card X = Nat.card (Set.range f) * Nat.card {z // f z = f x₀} := by
  let := (Set.finite_range f).fintype
  let fR : X → Set.range f := fun x => ⟨f x,⟨x,rfl⟩⟩
  have k (y : Set.range f) : Nat.card {x // fR x = y} =
      Nat.card {z // f z = f x₀} := by
    have hp (x : X) : fR x = y ↔ f x = y.1 := Subtype.ext_iff
    rw [Nat.card_congr (Equiv.subtypeEquivRight hp)]
    obtain ⟨x,hx⟩ := y.2
    rw [←hx]
    exact h x
  have hh := card_eq_mul_fiber fR (fR x₀) (fun y => by
    simpa only [←Nat.card_eq_fintype_card] using (k y).trans (k (fR x₀)).symm)
  have hh' : Nat.card X = Nat.card (Set.range f) * Nat.card {x // fR x = fR x₀} := by
    simpa only [←Nat.card_eq_fintype_card] using hh
  rw [k] at hh'
  simpa only [←Nat.card_eq_fintype_card] using hh'

variable {R I A B P : Type*} [Fintype I] [DecidableEq I]

variable [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] [Fintype P]

variable {s : ℕ}

section Group

variable {G : Type*} [Group G] [MulAction G A]

variable (S : Structure R A) (ep : P ⊕ Fin s ↪ I) (e2 : Fin s ⊕ Fin s ↪ I)

variable (hAut : ∀ (g : G) r a b, S.rel r (g • a) (g • b) ↔ S.rel r a b)

variable (p : P → A) (τ : Set (Formula R I))

include hAut in
omit [Fintype I] in


theorem uniform_value_fibers
    (hHom : ∀ a b : P ⊕ Fin s → A,
      tupleType S ep a = tupleType S ep b → ∃ g : G, ∀ i, g • a i = b i)
    (φ : Form (Fin s) (Set (Formula R I))) (a a' : Molecules S ep p τ) :
    Fintype.card {b : Molecules S ep p τ // Form.value S e2 φ b.1 = Form.value S e2 φ a.1} =
    Fintype.card {b : Molecules S ep p τ // Form.value S e2 φ b.1 = Form.value S e2 φ a'.1} := by
  obtain ⟨g,hg⟩ := hHom (Sum.elim p a.1) (Sum.elim p a'.1) (a.2.trans a'.2.symm)
  have hp : ∀ i, g • p i = p i := fun i => hg (.inl i)
  have ha : (fun i => g • a.1 i) = a'.1 := funext (fun i => hg (.inr i))
  let f := moleculesPerm S ep hAut p τ g hp
  have hv (b : Molecules S ep p τ) :
      Form.value S e2 φ (f b).1 = g • Form.value S e2 φ b.1 := by
    exact (value_smul S e2 hAut g φ b.1).symm
  have hv' : Form.value S e2 φ a'.1 = g • Form.value S e2 φ a.1 := by
    rw [←ha]
    exact (value_smul S e2 hAut g φ a.1).symm
  apply Fintype.card_congr
  apply f.subtypeEquiv
  intro b
  rw [hv,hv']
  exact (MulAction.injective g).eq_iff.symm

include hAut in
omit [Fintype I] in
private theorem label_orbit
    (hHom : ∀ a b : P ⊕ Fin s → A,
      tupleType S ep a = tupleType S ep b → ∃ g : G, ∀ i, g • a i = b i)
    (φ : Form (Fin s) (Set (Formula R I))) (x y : HF A)
    (hx : x ∈ labelValues S ep e2 p τ φ) (hy : y ∈ labelValues S ep e2 p τ φ) :
    ∃ g : G, (∀ i, g • p i = p i) ∧ g • x = y := by
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨b,rfl⟩ := hy
  obtain ⟨g,hg⟩ := hHom (Sum.elim p a.1) (Sum.elim p b.1) (a.2.trans b.2.symm)
  refine ⟨g,fun i => hg (.inl i),?_⟩
  rw [value_smul S e2 hAut]
  exact congrArg (Form.value S e2 φ) (funext (fun i => hg (.inr i)))

include hAut in
omit [Fintype I] in
private theorem label_smul_mem (g : G) (hp : ∀ i, g • p i = p i)
    (φ : Form (Fin s) (Set (Formula R I))) (x : HF A)
    (hx : x ∈ labelValues S ep e2 p τ φ) : g • x ∈ labelValues S ep e2 p τ φ := by
  obtain ⟨a,rfl⟩ := hx
  refine ⟨moleculesPerm S ep hAut p τ g hp a,?_⟩
  exact (value_smul S e2 hAut g φ a.1).symm

include hAut in
omit [Fintype I] in


theorem label_partition
    (hHom : ∀ a b : P ⊕ Fin s → A,
      tupleType S ep a = tupleType S ep b → ∃ g : G, ∀ i, g • a i = b i)
    (φ ψ : Form (Fin s) (Set (Formula R I))) (σ : Set (Formula R I)) (x : HF A)
    (hx : x ∈ labelValues S ep e2 p τ φ) (hx' : x ∈ labelValues S ep e2 p σ ψ) :
    labelValues S ep e2 p τ φ = labelValues S ep e2 p σ ψ := by
  ext y
  constructor
  · intro hy
    obtain ⟨g,hp,hg⟩ := label_orbit S ep e2 hAut p τ hHom φ x y hx hy
    rw [←hg]
    exact label_smul_mem S ep e2 hAut p σ g hp ψ x hx'
  · intro hy
    obtain ⟨g,hp,hg⟩ := label_orbit S ep e2 hAut p σ hHom ψ x y hx' hy
    rw [←hg]
    exact label_smul_mem S ep e2 hAut p τ g hp φ x hx

end Group


variable (S : Structure R A) (T : Structure R B)

variable (ep : P ⊕ Fin s ↪ I) (epp : (P ⊕ Fin s) ⊕ Fin s ↪ I)

variable (e2 : Fin s ⊕ Fin s ↪ I)

variable (e3 : (Fin s ⊕ Fin s) ⊕ Fin s ↪ I)

variable (e4 : ((Fin s ⊕ Fin s) ⊕ Fin s) ⊕ Fin s ↪ I)

include epp e3 e4 in




theorem value_fiber_equiv (p : P → A) (q : P → B) (τ : Set (Formula R I))
    (φ : Form (Fin s) (Set (Formula R I)))
    (a : Molecules S ep p τ) (a' : Molecules T ep q τ) :
    Nonempty ({b : Molecules S ep p τ // Form.value S e2 φ b.1 = Form.value S e2 φ a.1} ≃
    {b : Molecules T ep q τ // Form.value T e2 φ b.1 = Form.value T e2 φ a'.1}) := by
  obtain ⟨f,hf⟩ := tupleType_append_bijection S T ep epp
    (Sum.elim p a.1) (Sum.elim q a'.1) (a.2.trans a'.2.symm)
  have htype (b : Fin s → A) : tupleType S ep (Sum.elim p b) =
      tupleType T ep (Sum.elim q (f b)) := by
    have hh := tupleType_project S T epp ep skipMiddle _ _ (hf b)
    simpa only [elim_skipMiddle] using hh
  have hval (b : Fin s → A) : Form.value S e2 φ b = Form.value S e2 φ a.1 ↔
      Form.value T e2 φ (f b) = Form.value T e2 φ a'.1 := by
    have hh := tupleType_project S T epp e2 lastTwo _ _ (hf b)
    simp only [elim_lastTwo] at hh
    simpa only [eq_comm] using equality_transfer S T e2 e3 e4 φ φ a.1 b a'.1 (f b) hh
  let F : {b : Fin s → A // tupleType S ep (Sum.elim p b) = τ ∧
      Form.value S e2 φ b = Form.value S e2 φ a.1} ≃
      {b : Fin s → B // tupleType T ep (Sum.elim q b) = τ ∧
      Form.value T e2 φ b = Form.value T e2 φ a'.1} := f.subtypeEquiv (fun b => show
      (tupleType S ep (Sum.elim p b) = τ ∧ Form.value S e2 φ b = Form.value S e2 φ a.1) ↔
      (tupleType T ep (Sum.elim q (f b)) = τ ∧ Form.value T e2 φ (f b) = Form.value T e2 φ a'.1)
    from and_congr (by rw [htype b]) (hval b))
  exact ⟨(Equiv.subtypeSubtypeEquivSubtypeInter _ _).trans
    (F.trans (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm)⟩

include epp e3 e4 in


theorem label_overlap_transfer (e0 : P ↪ I) (p : P → A) (q : P → B)
    (hp : tupleType S e0 p = tupleType T e0 q)
    (φ ψ : Form (Fin s) (Set (Formula R I))) (τ σ : Set (Formula R I))
    (hx : ∃ x, x ∈ labelValues S ep e2 p τ φ ∧ x ∈ labelValues S ep e2 p σ ψ) :
    ∃ y, y ∈ labelValues T ep e2 q τ φ ∧ y ∈ labelValues T ep e2 q σ ψ := by
  obtain ⟨x,⟨a,ha⟩,⟨b,hb⟩⟩ := hx
  obtain ⟨a',ha'⟩ := tupleType_append S T e0 ep p q a.1 hp
  obtain ⟨b',hb'⟩ := tupleType_append S T ep epp
    (Sum.elim p a.1) (Sum.elim q a') b.1 ha'
  have ht := tupleType_project S T epp ep skipMiddle _ _ hb'
  simp only [elim_skipMiddle] at ht
  have he := tupleType_project S T epp e2 lastTwo _ _ hb'
  simp only [elim_lastTwo] at he
  have hv := (equality_transfer S T e2 e3 e4 φ ψ a.1 b.1 a' b' he).mp (ha.trans hb.symm)
  refine ⟨Form.value T e2 φ a',?_,?_⟩
  · exact ⟨⟨a',ha'.symm.trans a.2⟩,rfl⟩
  · exact ⟨⟨b',ht.symm.trans b.2⟩,hv.symm⟩

include epp e3 e4 in



theorem label_values_card
    {G H : Type*} [Group G] [MulAction G A] [Group H] [MulAction H B]
    (hAutA : ∀ (g : G) r a b, S.rel r (g • a) (g • b) ↔ S.rel r a b)
    (hAutB : ∀ (g : H) r a b, T.rel r (g • a) (g • b) ↔ T.rel r a b)
    (hHomA : ∀ a b : P ⊕ Fin s → A,
      tupleType S ep a = tupleType S ep b → ∃ g : G, ∀ i, g • a i = b i)
    (hHomB : ∀ a b : P ⊕ Fin s → B,
      tupleType T ep a = tupleType T ep b → ∃ g : H, ∀ i, g • a i = b i)
    (p : P → A) (q : P → B) (τ : Set (Formula R I))
    (φ : Form (Fin s) (Set (Formula R I)))
    (a : Molecules S ep p τ) (a' : Molecules T ep q τ) :
    Nat.card (labelValues S ep e2 p τ φ) = Nat.card (labelValues T ep e2 q τ φ) := by
  let va : Molecules S ep p τ → HF A := fun b => Form.value S e2 φ b.1
  let vb : Molecules T ep q τ → HF B := fun b => Form.value T e2 φ b.1
  have ha := range_card_mul_fiber va a (fun b => by simpa only [←Nat.card_eq_fintype_card] using uniform_value_fibers S ep e2 hAutA p τ hHomA φ b a)
  have hb := range_card_mul_fiber vb a' (fun b => by simpa only [←Nat.card_eq_fintype_card] using uniform_value_fibers T ep e2 hAutB q τ hHomB φ b a')
  let e0 := Function.Embedding.inl.trans ep
  have hp := tupleType_project S T ep e0 Function.Embedding.inl
    (Sum.elim p a.1) (Sum.elim q a'.1) (a.2.trans a'.2.symm)
  change tupleType S e0 p = tupleType T e0 q at hp
  obtain ⟨f⟩ := tupleType_extension_equiv S T e0 ep p q hp τ
  have hn : Fintype.card (Molecules S ep p τ) = Fintype.card (Molecules T ep q τ) :=
    Fintype.card_congr f
  obtain ⟨fv⟩ := value_fiber_equiv S T ep epp e2 e3 e4 p q τ φ a a'
  have he : Nat.card {b // va b = va a} = Nat.card {b // vb b = vb a'} :=
    Nat.card_congr fv
  have hpos : 0 < Nat.card {b // va b = va a} := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos_iff.mpr ⟨⟨a,rfl⟩⟩
  have hc := ha.symm.trans (hn.trans hb)
  rw [←he] at hc
  have hh := Nat.eq_of_mul_eq_mul_right hpos hc
  simpa only [←Nat.card_eq_fintype_card,labelValues,va,vb] using hh


end

end WitnessedSeparation.Forms



namespace WitnessedSeparation

noncomputable section

open Classical

theorem glue_finite_cells {L X Y : Type*} (C : L → Set X) (D : L → Set Y)
    (coverC : ∀ x, ∃ l, x ∈ C l) (coverD : ∀ y, ∃ l, y ∈ D l)
    (partC : ∀ l k x, x ∈ C l → x ∈ C k → C l = C k)
    (partD : ∀ l k y, y ∈ D l → y ∈ D k → D l = D k)
    (same : ∀ l k, C l = C k ↔ D l = D k)
    (finC : ∀ l, (C l).Finite) (finD : ∀ l, (D l).Finite)
    (card : ∀ l, Nat.card (C l) = Nat.card (D l)) :
    ∃ f : X ≃ Y, ∀ x, ∃ l, x ∈ C l ∧ f x ∈ D l := by
  let Q := Quotient (cellSetoid C)
  let lc : X → L := fun x => (coverC x).choose
  let ld : Y → L := fun y => (coverD y).choose
  have hc (x : X) : x ∈ C (lc x) := (coverC x).choose_spec
  have hd (y : Y) : y ∈ D (ld y) := (coverD y).choose_spec
  let c : X → Q := fun x => Quotient.mk _ (lc x)
  let d : Y → Q := fun y => Quotient.mk _ (ld y)
  have ce (x : X) (q : Q) : c x = q ↔ x ∈ C q.out := by
    constructor
    · intro h
      have he : C (lc x) = C q.out := Quotient.exact (h.trans (Quotient.out_eq q).symm)
      rw [←he]; exact hc x
    · intro h
      have he := partC (lc x) q.out x (hc x) h
      exact (Quotient.sound he).trans (Quotient.out_eq q)
  have de (y : Y) (q : Q) : d y = q ↔ y ∈ D q.out := by
    constructor
    · intro h
      have he : C (ld y) = C q.out := Quotient.exact (h.trans (Quotient.out_eq q).symm)
      rw [←(same _ _).mp he]; exact hd y
    · intro h
      have he := (same _ _).mpr (partD (ld y) q.out y (hd y) h)
      exact (Quotient.sound he).trans (Quotient.out_eq q)
  have ef (q : Q) : Nonempty ({x // c x = q} ≃ {y // d y = q}) := by
    let := (finC q.out).fintype
    let := (finD q.out).fintype
    have hcard : Fintype.card (C q.out) = Fintype.card (D q.out) := by
      simpa only [Nat.card_eq_fintype_card] using card q.out
    let e := Fintype.equivOfCardEq hcard
    exact ⟨(Equiv.subtypeEquivRight (fun x => ce x q)).trans
      (e.trans (Equiv.subtypeEquivRight (fun y => de y q)).symm)⟩
  let F := Equiv.ofFiberEquiv (fun q => Classical.choice (ef q))
  refine ⟨F,fun x => ⟨(c x).out,(ce x (c x)).mp rfl,?_⟩⟩
  apply (de (F x) (c x)).mp
  exact Equiv.ofFiberEquiv_map _ x

end

end WitnessedSeparation

end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_FormTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace WitnessedSeparation.Forms

noncomputable section

open Classical Counting Hereditary

variable {R I A B P G H : Type*}

variable [Fintype I] [DecidableEq I] [Fintype A] [Fintype B]

variable [Nonempty A] [Nonempty B] [Fintype P]

variable [Group G] [MulAction G A] [Group H] [MulAction H B]

variable {s : ℕ}

variable (S : Structure R A) (T : Structure R B)

variable (ep : P ⊕ Fin s ↪ I) (epp : (P ⊕ Fin s) ⊕ Fin s ↪ I)

variable (e2 : Fin s ⊕ Fin s ↪ I) (e3 : (Fin s ⊕ Fin s) ⊕ Fin s ↪ I)

variable (e4 : ((Fin s ⊕ Fin s) ⊕ Fin s) ⊕ Fin s ↪ I)

variable (hAutA : ∀ (g : G) r a b, S.rel r (g • a) (g • b) ↔ S.rel r a b)

variable (hAutB : ∀ (g : H) r a b, T.rel r (g • a) (g • b) ↔ T.rel r a b)

include hAutA in
omit [Fintype I] in
private theorem cell_finite (p : P → A) (φ : Form (Fin s) (Set (Formula R I))) (τ : Set (Formula R I)) :
    (Cell (G := G) S ep e2 p φ τ).Finite := by
  let := Fintype.ofEquiv (labelValues S ep e2 p τ φ) (cellEquiv S ep e2 hAutA p φ τ).symm
  exact Set.toFinite _

include hAutA hAutB epp e3 e4 in




theorem supported_domain_bijection (hs : 0 < s) (e0 : P ↪ I)
    (hHomA2 : ∀ a b : Fin s ⊕ Fin s → A,
      tupleType S e2 a = tupleType S e2 b → ∃ g : G, ∀ i, g • a i = b i)
    (hHomB2 : ∀ a b : Fin s ⊕ Fin s → B,
      tupleType T e2 a = tupleType T e2 b → ∃ g : H, ∀ i, g • a i = b i)
    (hHomA : ∀ a b : P ⊕ Fin s → A,
      tupleType S ep a = tupleType S ep b → ∃ g : G, ∀ i, g • a i = b i)
    (hHomB : ∀ a b : P ⊕ Fin s → B,
      tupleType T ep a = tupleType T ep b → ∃ g : H, ∀ i, g • a i = b i)
    (p : P → A) (q : P → B) (hp : tupleType S e0 p = tupleType T e0 q) :
    ∃ f : Domain (A := A) G s ≃ Domain (A := B) H s,
      ∀ x, ∃ φ : Form (Fin s) (Set (Formula R I)), ∃ a : Fin s → A, ∃ b : Fin s → B,
        Form.value S e2 φ a = x.1 ∧ Form.value T e2 φ b = (f x).1 ∧
        tupleType S ep (Sum.elim p a) = tupleType T ep (Sum.elim q b) := by
  let L := {l : Form (Fin s) (Set (Formula R I)) × Set (Formula R I) //
    Nonempty (Molecules S ep p l.2)}
  let C : L → Set (Domain (A := A) G s) := fun l => Cell S ep e2 p l.1.1 l.1.2
  let D : L → Set (Domain (A := B) H s) := fun l => Cell T ep e2 q l.1.1 l.1.2
  have nonemptyB (l : L) : Nonempty (Molecules T ep q l.1.2) := by
    obtain ⟨f⟩ := tupleType_extension_equiv S T e0 ep p q hp l.1.2
    exact Nonempty.map f l.2
  have coverC : ∀ x, ∃ l, x ∈ C l := by
    intro x
    obtain ⟨φ,a,ha⟩ := representation S e2 hAutA hs hHomA2 x.1 x.2
    let τ := tupleType S ep (Sum.elim p a)
    let l : L := ⟨(φ,τ),⟨⟨a,rfl⟩⟩⟩
    exact ⟨l,⟨⟨a,rfl⟩,ha⟩⟩
  have coverD : ∀ y, ∃ l, y ∈ D l := by
    intro y
    obtain ⟨φ,b,hb⟩ := representation T e2 hAutB hs hHomB2 y.1 y.2
    obtain ⟨a,ha⟩ := tupleType_append T S e0 ep q p b hp.symm
    let τ := tupleType T ep (Sum.elim q b)
    let l : L := ⟨(φ,τ),⟨⟨a,ha.symm⟩⟩⟩
    exact ⟨l,⟨⟨b,rfl⟩,hb⟩⟩
  have partC : ∀ l k x, x ∈ C l → x ∈ C k → C l = C k := by
    intro l k x hx hk
    have hh := label_partition S ep e2 hAutA p l.1.2 hHomA l.1.1 k.1.1 k.1.2 x.1 hx hk
    exact congrArg (fun Z : Set (HF A) => {x : Domain G s | x.1 ∈ Z}) hh
  have partD : ∀ l k x, x ∈ D l → x ∈ D k → D l = D k := by
    intro l k x hx hk
    have hh := label_partition T ep e2 hAutB q l.1.2 hHomB l.1.1 k.1.1 k.1.2 x.1 hx hk
    exact congrArg (fun Z : Set (HF B) => {x : Domain H s | x.1 ∈ Z}) hh
  have same : ∀ l k, C l = C k ↔ D l = D k := by
    intro l k
    constructor
    · intro he
      obtain ⟨a⟩ := l.2
      let x : Domain G s := ⟨Form.value S e2 l.1.1 a.1,
        value_hereditarily_supported S e2 hAutA _ _⟩
      have hx : x ∈ C l := ⟨a,rfl⟩
      have hk : x ∈ C k := he ▸ hx
      obtain ⟨y,hy,hy'⟩ := label_overlap_transfer S T ep epp e2 e3 e4 e0 p q hp
        l.1.1 k.1.1 l.1.2 k.1.2 ⟨x.1,hx,hk⟩
      have hsupp : HereditarilySupported (G := H) s y := by
        obtain ⟨b,rfl⟩ := hy
        exact value_hereditarily_supported T e2 hAutB _ _
      exact partD l k ⟨y,hsupp⟩ hy hy'
    · intro he
      obtain ⟨b⟩ := nonemptyB l
      let y : Domain H s := ⟨Form.value T e2 l.1.1 b.1,
        value_hereditarily_supported T e2 hAutB _ _⟩
      have hy : y ∈ D l := ⟨b,rfl⟩
      have hk : y ∈ D k := he ▸ hy
      obtain ⟨x,hx,hx'⟩ := label_overlap_transfer T S ep epp e2 e3 e4 e0 q p hp.symm
        l.1.1 k.1.1 l.1.2 k.1.2 ⟨y.1,hy,hk⟩
      have hsupp : HereditarilySupported (G := G) s x := by
        obtain ⟨a,rfl⟩ := hx
        exact value_hereditarily_supported S e2 hAutA _ _
      exact partC l k ⟨x,hsupp⟩ hx hx'
  have card : ∀ l, Nat.card (C l) = Nat.card (D l) := by
    intro l
    obtain ⟨a⟩ := l.2
    obtain ⟨b⟩ := nonemptyB l
    have hh := label_values_card S T ep epp e2 e3 e4 hAutA hAutB hHomA hHomB
      p q l.1.2 l.1.1 a b
    have he := Nat.card_congr (cellEquiv S ep e2 hAutA p l.1.1 l.1.2)
    have hf := Nat.card_congr (cellEquiv T ep e2 hAutB q l.1.1 l.1.2)
    exact he.trans (hh.trans hf.symm)
  obtain ⟨f,hf⟩ := WitnessedSeparation.glue_finite_cells C D coverC coverD partC partD same
    (fun l => cell_finite S ep e2 hAutA p l.1.1 l.1.2)
    (fun l => cell_finite T ep e2 hAutB q l.1.1 l.1.2) card
  refine ⟨f,fun x => ?_⟩
  obtain ⟨l,⟨a,ha⟩,⟨b,hb⟩⟩ := hf x
  exact ⟨l.1.1,a.1,b.1,ha,hb,a.2.trans b.2.symm⟩

end





noncomputable section

open Classical Counting Hereditary

variable {R I A B V G H : Type*}

variable [Fintype I] [DecidableEq I] [Fintype A] [Fintype B]

variable [Nonempty A] [Nonempty B] [Fintype V] [DecidableEq V]

variable [Group G] [MulAction G A] [Group H] [MulAction H B]

variable {s : ℕ}

variable (S : Structure R A) (T : Structure R B)

variable (ef : V × Fin s ↪ I) (e2 : Fin s ⊕ Fin s ↪ I)

variable (e3 : (Fin s ⊕ Fin s) ⊕ Fin s ↪ I)

variable (e4 : ((Fin s ⊕ Fin s) ⊕ Fin s) ⊕ Fin s ↪ I)

include e3 e4 in
theorem represented_equal (v : V → Domain (A := A) G s) (w : V → Domain (A := B) H s)
    (h : Represented S T ef e2 v w) (i j : V) : v i = v j ↔ w i = w j := by
  by_cases hij : i = j
  · subst j; simp
  obtain ⟨φ,a,b,ha,hb,ht⟩ := h
  have hh := tupleType_project S T ef e2 (twoBlocks i j hij) a b ht
  simp only [comp_twoBlocks] at hh
  have he := equality_transfer S T e2 e3 e4 (φ i) (φ j) _ _ _ _ hh
  simpa only [ha,hb,Subtype.ext_iff] using he

include e3 e4 in
theorem represented_mem (v : V → Domain (A := A) G s) (w : V → Domain (A := B) H s)
    (h : Represented S T ef e2 v w) (i j : V) : (v i).1 ∈ (v j).1 ↔ (w i).1 ∈ (w j).1 := by
  by_cases hij : i = j
  · subst j
    exact iff_of_false (fun h => (Nat.lt_irrefl _ (rank_lt_of_mem h)))
      (fun h => (Nat.lt_irrefl _ (rank_lt_of_mem h)))
  obtain ⟨φ,a,b,ha,hb,ht⟩ := h
  have hh := tupleType_project S T ef e2 (twoBlocks i j hij) a b ht
  simp only [comp_twoBlocks] at hh
  have he := membership_transfer S T e2 e3 e4 (φ i) (φ j) _ _ _ _ hh
  simpa only [ha,hb] using he

omit [Fintype I] [DecidableEq V] in
theorem represented_atom (v : V → Domain (A := A) G s) (w : V → Domain (A := B) H s)
    (h : Represented S T ef e2 v w) (i : V) : isSet (v i).1 = false ↔ isSet (w i).1 = false := by
  obtain ⟨φ,a,b,ha,hb,ht⟩ := h
  rw [←ha i,←hb i]
  cases φ i <;> simp

omit [Fintype I] in
private theorem base_value (φ ψ : Form (Fin s) (Set (Formula R I)))
    (a b : Fin s → A) (r : R) :
    (∃ x y, Form.value S e2 φ a = Hereditary.atom x ∧
      Form.value S e2 ψ b = Hereditary.atom y ∧ S.rel r x y) ↔
    match φ,ψ with
    | .atom i, .atom j => S.rel r (a i) (b j)
    | _, _ => False := by
  have hn (n : ℕ) (child : Fin n → Form (Fin s) (Set (Formula R I)))
      (label : Fin n → Set (Formula R I)) (c : Fin s → A) (x : A) :
      Form.value S e2 (.set n child label) c ≠ Hereditary.atom x := by
    intro h; have hh := congrArg isSet h; simp at hh
  cases φ <;> cases ψ <;> simp [Form.value_atom,atom_injective.eq_iff,hn]

omit [DecidableEq V] in
omit [Fintype I] in
theorem represented_base (v : V → Domain (A := A) G s) (w : V → Domain (A := B) H s)
    (h : Represented S T ef e2 v w) (r : R) (i j : V) :
    (hfStructure S).rel (.base r) (v i) (v j) ↔ (hfStructure T).rel (.base r) (w i) (w j) := by
  obtain ⟨φ,a,b,ha,hb,ht⟩ := h
  change (∃ x y, (v i).1 = Hereditary.atom x ∧ (v j).1 = Hereditary.atom y ∧ S.rel r x y) ↔
    (∃ x y, (w i).1 = Hereditary.atom x ∧ (w j).1 = Hereditary.atom y ∧ T.rel r x y)
  rw [←ha i,←ha j,←hb i,←hb j,base_value S e2,base_value T e2]
  cases hi : φ i with
  | set n child label => simp
  | atom k =>
    cases hj : φ j with
    | set n child label => simp
    | atom l =>
      have he := (typeOf_eq_iff S T (tupleNames ef) _ _).mp ht
        (.relation r (ef (i,k)) (ef (j,l))) (by
          intro p hp
          simp only [Formula.free,Finset.mem_insert,Finset.mem_singleton] at hp
          rcases hp with rfl | rfl <;> exact (mem_tupleNames _ _).mpr ⟨_,rfl⟩)
      simpa only [Formula.eval,tupleAssignment_apply] using he

omit [Fintype I] [Fintype A] in
private theorem homogeneity_reindex {J K : Type*} [Fintype J] [Fintype K]
    (S : Structure R A) (e : J ↪ I) (f : K ↪ I) (u : K ≃ J)
    (hh : ∀ a b : J → A, tupleType S e a = tupleType S e b →
      ∃ g : G, ∀ j, g • a j = b j) :
    ∀ a b : K → A, tupleType S f a = tupleType S f b → ∃ g : G, ∀ j, g • a j = b j := by
  intro a b hab
  have h := tupleType_project S S f e u.symm.toEmbedding a b hab
  obtain ⟨g,hg⟩ := hh _ _ h
  exact ⟨g,fun j => by simpa using hg (u j)⟩

variable (eplus : (V × Fin s) ⊕ Fin s ↪ I)

variable (hAutA : ∀ (g : G) r a b, S.rel r (g • a) (g • b) ↔ S.rel r a b)

variable (hAutB : ∀ (g : H) r a b, T.rel r (g • a) (g • b) ↔ T.rel r a b)

include eplus e3 e4 hAutA hAutB in


theorem represented_extension (hs : 0 < s)
    (hHomA2 : ∀ a b : Fin s ⊕ Fin s → A,
      tupleType S e2 a = tupleType S e2 b → ∃ g : G, ∀ i, g • a i = b i)
    (hHomB2 : ∀ a b : Fin s ⊕ Fin s → B,
      tupleType T e2 a = tupleType T e2 b → ∃ g : H, ∀ i, g • a i = b i)
    (hHomA : ∀ a b : V × Fin s → A,
      tupleType S ef a = tupleType S ef b → ∃ g : G, ∀ i, g • a i = b i)
    (hHomB : ∀ a b : V × Fin s → B,
      tupleType T ef a = tupleType T ef b → ∃ g : H, ∀ i, g • a i = b i)
    (v : V → Domain (A := A) G s) (w : V → Domain (A := B) H s)
    (h : Represented S T ef e2 v w) (i : V) :
    ∃ f : Domain (A := A) G s ≃ Domain (A := B) H s,
      ∀ x, Represented S T ef e2 (Function.update v i x) (Function.update w i (f x)) := by
  obtain ⟨φ,a,b,ha,hb,ht⟩ := h
  let P := {j : V // j ≠ i} × Fin s
  let u : P ⊕ Fin s ≃ V × Fin s := splitBlock i
  let ep := u.toEmbedding.trans ef
  let epp := (Equiv.sumCongr u (Equiv.refl (Fin s))).toEmbedding.trans eplus
  let e0 := Function.Embedding.inl.trans ep
  let keep : P ↪ V × Fin s := Function.Embedding.inl.trans u.toEmbedding
  let p : P → A := a ∘ keep
  let q : P → B := b ∘ keep
  have hp : tupleType S e0 p = tupleType T e0 q :=
    tupleType_project S T ef e0 keep a b ht
  have homA := homogeneity_reindex S ef ep u hHomA
  have homB := homogeneity_reindex T ef ep u hHomB
  obtain ⟨f,hf⟩ := supported_domain_bijection S T ep epp e2 e3 e4
    hAutA hAutB hs e0 hHomA2 hHomB2 homA homB p q hp
  refine ⟨f,fun x => ?_⟩
  obtain ⟨ψ,c,d,hc,hd,hcd⟩ := hf x
  let a' := Sum.elim p c ∘ u.symm
  let b' := Sum.elim q d ∘ u.symm
  refine ⟨Function.update φ i ψ,a',b',?_,?_,?_⟩
  · intro j
    by_cases hj : j = i
    · subst j
      simpa [a',u,Function.comp_def,splitBlock] using hc
    · simpa [a',u,p,keep,Function.comp_def,splitBlock_symm_old i j hj,
        Function.update_of_ne hj,splitBlock,hj] using ha j
  · intro j
    by_cases hj : j = i
    · subst j
      simpa [b',u,Function.comp_def,splitBlock] using hd
    · simpa [b',u,q,keep,Function.comp_def,splitBlock_symm_old i j hj,
        Function.update_of_ne hj,splitBlock,hj] using hb j
  · exact tupleType_project S T ep ef u.symm.toEmbedding _ _ hcd

include eplus e3 e4 hAutA hAutB in


theorem supported_eval_transfer (hs : 0 < s)
    (hHomA2 : ∀ a b : Fin s ⊕ Fin s → A,
      tupleType S e2 a = tupleType S e2 b → ∃ g : G, ∀ i, g • a i = b i)
    (hHomB2 : ∀ a b : Fin s ⊕ Fin s → B,
      tupleType T e2 a = tupleType T e2 b → ∃ g : H, ∀ i, g • a i = b i)
    (hHomA : ∀ a b : V × Fin s → A,
      tupleType S ef a = tupleType S ef b → ∃ g : G, ∀ i, g • a i = b i)
    (hHomB : ∀ a b : V × Fin s → B,
      tupleType T ef a = tupleType T ef b → ∃ g : H, ∀ i, g • a i = b i)
    (φ : Formula (HFRelation R) V)
    (v : V → Domain (A := A) G s) (w : V → Domain (A := B) H s)
    (h : Represented S T ef e2 v w) :
    φ.eval (hfStructure S) v ↔ φ.eval (hfStructure T) w := by
  apply Formula.eval_of_bijectionSystem (hfStructure S) (hfStructure T)
    (Represented S T ef e2) _ _ _ φ v w h
  · exact represented_equal S T ef e2 e3 e4
  · intro v w h r i j
    cases r with
    | mem => exact represented_mem S T ef e2 e3 e4 v w h i j
    | atom => exact represented_atom S T ef e2 v w h i
    | base r => exact represented_base S T ef e2 v w h r i j
  · exact represented_extension S T ef e2 e3 e4 eplus hAutA hAutB hs
      hHomA2 hHomB2 hHomA hHomB

include eplus e3 e4 hAutA hAutB in


theorem supported_sentences_transfer (hs : 0 < s)
    (hHomA2 : ∀ a b : Fin s ⊕ Fin s → A,
      tupleType S e2 a = tupleType S e2 b → ∃ g : G, ∀ i, g • a i = b i)
    (hHomB2 : ∀ a b : Fin s ⊕ Fin s → B,
      tupleType T e2 a = tupleType T e2 b → ∃ g : H, ∀ i, g • a i = b i)
    (hHomA : ∀ a b : V × Fin s → A,
      tupleType S ef a = tupleType S ef b → ∃ g : G, ∀ i, g • a i = b i)
    (hHomB : ∀ a b : V × Fin s → B,
      tupleType T ef a = tupleType T ef b → ∃ g : H, ∀ i, g • a i = b i)
    (hbase : tupleType S (Function.Embedding.ofIsEmpty : Empty ↪ I) Empty.elim =
      tupleType T (Function.Embedding.ofIsEmpty : Empty ↪ I) Empty.elim)
    (φ : Formula (HFRelation R) V) (hφ : φ.free = ∅)
    (v : V → Domain (A := A) G s) (w : V → Domain (A := B) H s) :
    φ.eval (hfStructure S) v ↔ φ.eval (hfStructure T) w := by
  let a : V × Fin s → A := fun _ => Classical.choice inferInstance
  have he : tupleType S (Function.Embedding.ofIsEmpty : Empty ↪ I)
      (a ∘ (Function.Embedding.ofIsEmpty : Empty ↪ V × Fin s)) =
        tupleType T (Function.Embedding.ofIsEmpty : Empty ↪ I) Empty.elim := by
    convert hbase using 1
    congr 1; funext x; exact x.elim
  obtain ⟨b,_,hab⟩ := tupleType_extend S T
    (Function.Embedding.ofIsEmpty : Empty ↪ I) ef
    (Function.Embedding.ofIsEmpty : Empty ↪ V × Fin s) a Empty.elim he
  let emptyForm : Form (Fin s) (Set (Formula R I)) := .set 0 Fin.elim0 Fin.elim0
  let v' : V → Domain (A := A) G s := fun i =>
    ⟨Form.value S e2 emptyForm (fun j => a (i,j)),
      value_hereditarily_supported S e2 hAutA emptyForm _⟩
  let w' : V → Domain (A := B) H s := fun i =>
    ⟨Form.value T e2 emptyForm (fun j => b (i,j)),
      value_hereditarily_supported T e2 hAutB emptyForm _⟩
  have hr : Represented S T ef e2 v' w' :=
    ⟨(fun _ => emptyForm),a,b,(fun _ => rfl),(fun _ => rfl),hab⟩
  have hh := supported_eval_transfer S T ef e2 e3 e4 eplus hAutA hAutB hs
    hHomA2 hHomB2 hHomA hHomB φ v' w' hr
  exact (Formula.eval_congr _ φ (fun i hi => by simp [hφ] at hi)).trans
    (hh.trans (Formula.eval_congr _ φ (fun i hi => by simp [hφ] at hi)))

omit [Fintype A] in
private theorem homogeneous_tuple {J : Type*} [Fintype J] {M r : ℕ}
    (S : Structure R A) (G : Type*) [Group G] [MulAction G A]
    (h : HomogeneousThrough S G M r) (e : J ↪ Fin M)
    (hc : Fintype.card J ≤ r) :
    ∀ a b : J → A, tupleType S e a = tupleType S e b → ∃ g : G, ∀ j, g • a j = b j := by
  exact homogeneity_reindex S ((Fintype.equivFin J).symm.toEmbedding.trans e) e
    (Fintype.equivFin J) (h _ hc _)

theorem hf_transfer {m M : ℕ} (hs : 0 < s) (_hm : 0 < m) (hM : 0 < M)
    (hwidth : max 4 (m+1) * s ≤ M)
    (hAutA : ∀ (g : G) r a b, S.rel r (g • a) (g • b) ↔ S.rel r a b)
    (hAutB : ∀ (g : H) r a b, T.rel r (g • a) (g • b) ↔ T.rel r a b)
    (hHomA : HomogeneousThrough S G M (max 2 m * s))
    (hHomB : HomogeneousThrough T H M (max 2 m * s))
    (hbase : tupleType S (Function.Embedding.ofIsEmpty : Empty ↪ Fin M) Empty.elim =
      tupleType T (Function.Embedding.ofIsEmpty : Empty ↪ Fin M) Empty.elim)
    (φ : Formula (HFRelation R) (Fin m)) (hφ : φ.free = ∅)
    (v : Fin m → Domain (A := A) G s) (w : Fin m → Domain (A := B) H s) :
    φ.eval (hfStructure S) v ↔ φ.eval (hfStructure T) w := by
  have h4 : 4*s ≤ M := (Nat.mul_le_mul_right s (le_max_left _ _)).trans hwidth
  have hp : (m+1)*s ≤ M := (Nat.mul_le_mul_right s (le_max_right _ _)).trans hwidth
  have h2 : Fintype.card (Fin s ⊕ Fin s) ≤ M := by simp only [Fintype.card_sum,Fintype.card_fin]; omega
  have h3 : Fintype.card ((Fin s ⊕ Fin s) ⊕ Fin s) ≤ M := by simp only [Fintype.card_sum,Fintype.card_fin]; omega
  have h4' : Fintype.card (((Fin s ⊕ Fin s) ⊕ Fin s) ⊕ Fin s) ≤ M := by simp only [Fintype.card_sum,Fintype.card_fin]; omega
  have hpf : Fintype.card ((Fin m × Fin s) ⊕ Fin s) ≤ M := by simpa [Nat.add_mul] using hp
  have hfull : Fintype.card (Fin m × Fin s) ≤ M := by simp only [Fintype.card_prod,Fintype.card_fin]; nlinarith
  have hom2 : Fintype.card (Fin s ⊕ Fin s) ≤ max 2 m*s := by
    simpa [two_mul] using Nat.mul_le_mul_right s (le_max_left 2 m)
  have homf : Fintype.card (Fin m × Fin s) ≤ max 2 m*s := by
    simpa using Nat.mul_le_mul_right s (le_max_right 2 m)
  exact supported_sentences_transfer S T (namesOfCard hfull) (namesOfCard h2)
    (namesOfCard h3) (namesOfCard h4') (namesOfCard hpf) hAutA hAutB hs
    (homogeneous_tuple S G hHomA _ hom2) (homogeneous_tuple T H hHomB _ hom2)
    (homogeneous_tuple S G hHomA _ homf) (homogeneous_tuple T H hHomB _ homf)
    hbase φ hφ v w

end

end WitnessedSeparation.Forms



namespace WitnessedSeparation.Hereditary

noncomputable section

variable {A G : Type*} [Group G] [MulAction G A]

theorem supports_pad {k s : ℕ} (hks : k ≤ s) (a₀ : A) (alpha : Fin k → A)
    {x : HF A} (h : Supports (G := G) alpha x) : Supported (G := G) s x := by
  classical
  let beta (i : Fin s) : A := if hi : i.val < k then alpha ⟨i.val,hi⟩ else a₀
  refine ⟨beta,?_⟩
  intro g hg
  apply h g
  intro i
  have hi := hg (i.castLE hks)
  simpa only [beta, Fin.val_castLE, dite_eq_left i.isLt] using hi

end

end WitnessedSeparation.Hereditary



namespace WitnessedSeparation.Grid

open Support Hereditary

noncomputable section

variable {n : ℕ} {b : Vertex n → Scalar}

theorem small_orbit_supported (hn : 1 ≤ n) (x : HF (Atom b))
    (N : ℕ) (hN : 0 < N) (q : ℝ) (hq : 0 ≤ q)
    (horbit : (Nat.card (MulAction.orbit (BoxGroup n) x) : ℝ) ≤ (N : ℝ)^q) :
    Supported (G := CentralGroup n) ⌈2 * (n+1 : ℝ) * (q * Real.logb 3 N)^2⌉₊ x := by
  classical
  obtain ⟨T,hT,hfix⟩ := small_orbit_support_edges x N hN q hq horbit
  obtain ⟨alpha,ha⟩ := edge_support_tuple (b := b) T x hfix
  have hsupport : Supports (G := CentralGroup n) alpha x := by
    intro k hk
    exact ha k hk
  have hlen : T.card ≤ ⌈2 * (n+1 : ℝ) * (q * Real.logb 3 N)^2⌉₊ := by
    exact_mod_cast le_trans hT (Nat.le_ceil _)
  let a₀ : Atom b := zeroEdgeAtom b (ex ⟨0,by omega⟩ 0 0)
  exact supports_pad hlen a₀ alpha hsupport

theorem orbit_card_le_invariant_family (F : Finset (HF (Atom b)))
    (hF : ∀ g : BoxGroup n, ∀ x ∈ F, g • x ∈ F) {x : HF (Atom b)} (hx : x ∈ F) :
    Nat.card (MulAction.orbit (BoxGroup n) x) ≤ F.card := by
  classical
  let f : MulAction.orbit (BoxGroup n) x → {y // y ∈ F} := fun y =>
    ⟨y.val,by obtain ⟨g,hg⟩ := y.property; rw [← hg]; exact hF g x hx⟩
  have hf : Function.Injective f := by
    intro a c h
    exact Subtype.ext (congrArg (fun z : {y // y ∈ F} => z.val) h)
  have hn := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hn

theorem invariant_family_hereditarily_supported (hn : 1 ≤ n)
    (F : Finset (HF (Atom b)))
    (hF : ∀ g : BoxGroup n, ∀ x ∈ F, g • x ∈ F)
    (htrans : ∀ x ∈ F, ∀ y, y ∈ x → y ∈ F)
    (N : ℕ) (hN : 0 < N) (q : ℝ) (hq : 0 ≤ q)
    (hsize : (F.card : ℝ) ≤ (N : ℝ)^q) :
    ∀ x ∈ F, HereditarilySupported (G := CentralGroup n)
      ⌈2 * (n+1 : ℝ) * (q * Real.logb 3 N)^2⌉₊ x := by
  intro x hx y hy
  have hymem : y ∈ F := by
    induction hy with
    | refl => exact hx
    | @tail z w hpath hmem ih => exact ih (htrans w hx z hmem)
  apply small_orbit_supported hn y N hN q hq
  exact le_trans (by exact_mod_cast orbit_card_le_invariant_family F hF hymem) hsize

end

end WitnessedSeparation.Grid



namespace WitnessedSeparation.Grid

noncomputable section

open Classical Finset

variable {n M m s : ℕ} {b : Vertex n → Scalar}

theorem atom_nonempty (hn : 1 ≤ n) (b : Vertex n → Scalar) : Nonempty (Atom b) :=
  ⟨.inr ⟨(0,0,0),someConfiguration hn b (0,0,0)⟩⟩

instance atom_nonempty_succ (b : Vertex (n+1) → Scalar) : Nonempty (Atom b) := atom_nonempty (by omega) b

theorem central_analysis_isomorphism (k : CentralGroup n) (r : AnalysisSymbol) (x y : Atom b) :
    (analysisStructure b).rel r (k • x) (k • y) ↔ (analysisStructure b).rel r x y :=
  ((central_atomShift k x).analysisRelation (central_atomShift k y) r).symm

theorem homogeneous_through_numeric (hn : 1 ≤ n) [Nonempty (Atom b)] (R : ℕ)
    (hw : (7*R:ℝ)+7*((6*R:ℝ)/boxConstant)^((3:ℝ)/2)+1 ≤ M) :
    Forms.HomogeneousThrough (analysisStructure b) (CentralGroup n) M R := by
  intro k hk names a a' ht
  apply quantitative_homogeneity hn names a a' _ ht
  simp only [Fintype.card_fin]
  have hkr : (k:ℝ) ≤ R := by exact_mod_cast hk
  have hp : ((6*k:ℝ)/boxConstant)^((3:ℝ)/2) ≤ ((6*R:ℝ)/boxConstant)^((3:ℝ)/2) := by
    apply Real.rpow_le_rpow (div_nonneg (by positivity) boxConstant_pos.le) _ (by norm_num)
    exact div_le_div_of_nonneg_right (by linarith) boxConstant_pos.le
  linarith

theorem base_empty_type (hn : 1 ≤ n) (hbound : GiantBound n M) (vstar : Vertex n)
    [Nonempty (Atom (0 : Vertex n → Scalar))] [Nonempty (Atom (Pi.single vstar 1))] :
    Counting.tupleType (analysisStructure (0 : Vertex n → Scalar))
      (Function.Embedding.ofIsEmpty : Empty ↪ Fin M) Empty.elim =
    Counting.tupleType (analysisStructure (Pi.single vstar 1))
      (Function.Embedding.ofIsEmpty : Empty ↪ Fin M) Empty.elim := by
  apply (Counting.typeOf_eq_iff _ _ _ _ _).mpr
  intro φ hφ
  have he : φ.free = ∅ := by
    apply subset_empty.mp
    simpa only [Counting.tupleNames,Finset.univ_eq_empty,Finset.map_empty] using hφ
  exact base_equivalence_numeric hn hbound vstar φ he _ _

theorem grid_hf_transfer (hn : 1 ≤ n) (hs : 0 < s) (hm : 0 < m)
    (vstar : Vertex n) [Nonempty (Atom (0 : Vertex n → Scalar))]
    [Nonempty (Atom (Pi.single vstar 1))]
    (hwidth : max 4 (m+1)*s ≤ M)
    (hhom : (7*(max 2 m*s):ℝ)+7*((6*(max 2 m*s):ℝ)/boxConstant)^((3:ℝ)/2)+1 ≤ M)
    (hgiant : GiantBound n M)
    (φ : Counting.Formula (Forms.HFRelation AnalysisSymbol) (Fin m)) (hφ : φ.free = ∅)
    (v : Fin m → Forms.Domain (A := Atom (0 : Vertex n → Scalar)) (CentralGroup n) s)
    (w : Fin m → Forms.Domain (A := Atom (Pi.single vstar 1)) (CentralGroup n) s) :
    φ.eval (Forms.hfStructure (analysisStructure (0 : Vertex n → Scalar))) v ↔
      φ.eval (Forms.hfStructure (analysisStructure (Pi.single vstar 1))) w := by
  have hM : 0 < M := lt_of_lt_of_le (Nat.mul_pos (by omega) hs) hwidth
  exact Forms.hf_transfer _ _ hs hm hM hwidth
    (fun g r a b => central_analysis_isomorphism g r a b)
    (fun g r a b => central_analysis_isomorphism g r a b)
    (homogeneous_through_numeric hn _ (by simpa only [Nat.cast_mul] using hhom))
    (homogeneous_through_numeric hn _ (by simpa only [Nat.cast_mul] using hhom))
    (base_empty_type hn hgiant vstar) φ hφ v w

end

end WitnessedSeparation.Grid



namespace WitnessedSeparation.Interpretations

attribute [instance] Structure.finite

end WitnessedSeparation.Interpretations



end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_CountingTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace WitnessedSeparation.Counting

noncomputable section

open Classical Finset

variable {R ι : Type*} {D : ι → Type*} (S : ∀ i, Structure R (D i)) {m n k : ℕ}

namespace UniformDefinable

variable {S} {P Q : ∀ i, (Fin n → D i) → Prop}

theorem relation (r : R) (a b : Fin n) :
    UniformDefinable S m n (fun i v => (S i).rel r (v a) (v b)) := by
  intro args
  refine ⟨.relation r (args a) (args b),?_,fun _ _ => Iff.rfl⟩
  simp only [Formula.free,insert_subset_iff,singleton_subset_iff]
  exact ⟨mem_image.mpr ⟨a,mem_univ _,rfl⟩,mem_image.mpr ⟨b,mem_univ _,rfl⟩⟩

end UniformDefinable

end

end WitnessedSeparation.Counting



end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_EncodedCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace WitnessedSeparation.Grid

noncomputable section

open Classical Finset Support

variable {n : ℕ}

private theorem four_fibers {α β : Type*} [Fintype α] [DecidableEq β]
    (f₀ f₁ f₂ f₃ : α → β) (h₀ : Function.Injective f₀) (h₁ : Function.Injective f₁)
    (h₂ : Function.Injective f₂) (h₃ : Function.Injective f₃) (e : β)
    (p : α → Prop) [DecidablePred p] (hp : ∀ a, p a → f₀ a = e ∨ f₁ a = e ∨ f₂ a = e ∨ f₃ a = e) :
    Fintype.card {a // p a} ≤ 4 := by
  have hcard (f : α → β) (hf : Function.Injective f) :
      (univ.filter (fun a => f a = e)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact hf ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm)
  rw [Fintype.card_subtype]
  have hs : univ.filter p ⊆
      ((univ.filter (fun a => f₀ a = e) ∪ univ.filter (fun a => f₁ a = e)) ∪
      univ.filter (fun a => f₂ a = e)) ∪ univ.filter (fun a => f₃ a = e) := by
    intro a ha
    have h := hp a (mem_filter.mp ha).2
    simpa only [mem_union,mem_filter,mem_univ,true_and,or_assoc] using h
  exact (card_le_card hs).trans (le_trans (card_union_le _ _) (by
    have h01 := card_union_le (univ.filter (fun a => f₀ a = e)) (univ.filter (fun a => f₁ a = e))
    have h012 := card_union_le
      (univ.filter (fun a => f₀ a = e) ∪ univ.filter (fun a => f₁ a = e))
      (univ.filter (fun a => f₂ a = e))
    have := hcard f₀ h₀; have := hcard f₁ h₁; have := hcard f₂ h₂; have := hcard f₃ h₃
    omega))

theorem edgeFaces_card_le (e : Edge n) : Fintype.card (EdgeFaces e) ≤ 12 := by
  have hxy : Fintype.card {f : FaceXY n // cycle (.inl f) e ≠ 0} ≤ 4 := by
    refine four_fibers (α := FaceXY n) (β := Edge n) (fun ⟨i,j,k⟩ => ex i j.castSucc k)
      (fun ⟨i,j,k⟩ => ey i.succ j k) (fun ⟨i,j,k⟩ => ex i j.succ k)
      (fun ⟨i,j,k⟩ => ey i.castSucc j k) ?_ ?_ ?_ ?_ e _ ?_
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ex] using h
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ey] using h
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ex] using h
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ey] using h
    · rintro ⟨i,j,k⟩ h
      by_contra hn
      push Not at hn
      apply h
      simp [cycle,Pi.single_eq_of_ne,Ne.symm hn.1,Ne.symm hn.2.1,
        Ne.symm hn.2.2.1,Ne.symm hn.2.2.2]
  have hxz : Fintype.card {f : FaceXZ n // cycle (.inr (.inl f)) e ≠ 0} ≤ 4 := by
    refine four_fibers (α := FaceXZ n) (β := Edge n) (fun ⟨i,j,k⟩ => ex i j k.castSucc)
      (fun ⟨i,j,k⟩ => ez i.succ j k) (fun ⟨i,j,k⟩ => ex i j k.succ)
      (fun ⟨i,j,k⟩ => ez i.castSucc j k) ?_ ?_ ?_ ?_ e _ ?_
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ex] using h
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ez] using h
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ex] using h
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ez] using h
    · rintro ⟨i,j,k⟩ h
      by_contra hn
      push Not at hn
      apply h
      simp [cycle,Pi.single_eq_of_ne,Ne.symm hn.1,Ne.symm hn.2.1,
        Ne.symm hn.2.2.1,Ne.symm hn.2.2.2]
  have hyz : Fintype.card {f : FaceYZ n // cycle (.inr (.inr f)) e ≠ 0} ≤ 4 := by
    refine four_fibers (α := FaceYZ n) (β := Edge n) (fun ⟨i,j,k⟩ => ey i j k.castSucc)
      (fun ⟨i,j,k⟩ => ez i j.succ k) (fun ⟨i,j,k⟩ => ey i j k.succ)
      (fun ⟨i,j,k⟩ => ez i j.castSucc k) ?_ ?_ ?_ ?_ e _ ?_
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ey] using h
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ez] using h
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ey] using h
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ez] using h
    · rintro ⟨i,j,k⟩ h
      by_contra hn
      push Not at hn
      apply h
      simp [cycle,Pi.single_eq_of_ne,Ne.symm hn.1,Ne.symm hn.2.1,
        Ne.symm hn.2.2.1,Ne.symm hn.2.2.2]
  unfold EdgeFaces Face
  rw [Fintype.card_congr Equiv.subtypeSum,Fintype.card_sum,
    Fintype.card_congr Equiv.subtypeSum,Fintype.card_sum]
  omega

theorem localGroup_card_le (e : Edge n) : Fintype.card (LocalGroup e) ≤ localSizeBound := by
  rw [Fintype.card_congr (Support.H.productEquiv (localCycle e)),Fintype.card_prod,
    Fintype.card_fun,Fintype.card_prod]
  have hf := edgeFaces_card_le e
  simp only [Scalar,ZMod.card] at *
  change (3*3)^Fintype.card (EdgeFaces e)*3 ≤ 3^25
  calc
    (3*3)^Fintype.card (EdgeFaces e)*3 ≤ (3*3)^12*3 :=
      Nat.mul_le_mul_right 3 (Nat.pow_le_pow_right (by norm_num) hf)
    _ = 3^25 := by norm_num

theorem configuration_card_le (b : Vertex n → Scalar) (v : Vertex n) :
    Fintype.card (Configuration b v) ≤ localSizeBound^6 := by
  have hi : Function.Injective (fun s : Configuration b v => s.state) :=
    fun s t h => Configuration.ext (congrFun h)
  have hdegree : Fintype.card (IncidentEdges v) ≤ 6 := degree_le_six v
  calc
    Fintype.card (Configuration b v) ≤ Fintype.card (LocalStates v) := Fintype.card_le_of_injective _ hi
    _ = ∏ e : IncidentEdges v, Fintype.card (LocalGroup e.val) := Fintype.card_pi
    _ ≤ ∏ _e : IncidentEdges v, localSizeBound := Finset.prod_le_prod' (fun e _ => localGroup_card_le e.val)
    _ = localSizeBound^Fintype.card (IncidentEdges v) := by simp
    _ ≤ localSizeBound^6 := Nat.pow_le_pow_right (by norm_num [localSizeBound]) hdegree

theorem atom_card_bounds (hn : 1 ≤ n) (b : Vertex n → Scalar) :
    (n+1)^3 ≤ Fintype.card (Atom b) ∧
    Fintype.card (Atom b) ≤ atomSizeConstant*(n+1)^3 := by
  have hv : Fintype.card (Vertex n) = (n+1)^3 := by simp [Vertex]; ring
  have he : Fintype.card (Edge n) ≤ 3*(n+1)^3 := by
    simp only [Edge,EdgeX,EdgeY,EdgeZ,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    nlinarith
  constructor
  · rw [← hv]
    apply Fintype.card_le_of_injective (fun v : Vertex n => (.inr ⟨v,someConfiguration hn b v⟩ : Atom b))
    intro v w h
    exact congrArg Sigma.fst (Sum.inr.inj h)
  · change Fintype.card ((Σ e : Edge n, LocalGroup e) ⊕ (Σ v : Vertex n, Configuration b v)) ≤ _
    rw [← Nat.card_eq_fintype_card, Nat.card_sum, Nat.card_sigma, Nat.card_sigma]
    simp only [Nat.card_eq_fintype_card]
    calc
      (∑ e : Edge n, Fintype.card (LocalGroup e))+
          ∑ v : Vertex n, Fintype.card (Configuration b v) ≤
          (∑ _e : Edge n, localSizeBound)+∑ _v : Vertex n, localSizeBound^6 :=
        add_le_add (sum_le_sum (fun e _ => localGroup_card_le e))
          (sum_le_sum (fun v _ => configuration_card_le b v))
      _ = Fintype.card (Edge n)*localSizeBound+Fintype.card (Vertex n)*localSizeBound^6 := by simp
      _ ≤ (3*(n+1)^3)*localSizeBound+(n+1)^3*localSizeBound^6 := by
        rw [hv]
        exact add_le_add (Nat.mul_le_mul_right _ he) (le_refl _)
      _ = atomSizeConstant*(n+1)^3 := by unfold atomSizeConstant; ring

end

end WitnessedSeparation.Grid



namespace WitnessedSeparation.Hereditary

noncomputable section

open Classical

variable {A G : Type*} [Group G] [MulAction G A] {s : ℕ}

theorem hereditary_iff {x : HF A} : HereditarilySupported (G := G) s x ↔
    Supported (G := G) s x ∧ ∀ y, y ∈ x → HereditarilySupported (G := G) s y := by
  constructor
  · intro h
    exact ⟨h x .refl,fun y hy z hz => h z (hz.tail hy)⟩
  · rintro ⟨h,hm⟩ y hy
    cases hy with
    | refl => exact h
    | tail hz hzx => exact hm _ hzx _ hz

theorem hereditary_transitive {x y : HF A} (hx : HereditarilySupported (G := G) s x) (hy : y ∈ x) :
    HereditarilySupported (G := G) s y := (hereditary_iff.mp hx).2 y hy

theorem ordinal_hereditary [Nonempty A] (s j : ℕ) :
    HereditarilySupported (G := G) s (ordinal (A := A) j) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    apply hereditary_iff.mpr
    constructor
    · refine ⟨fun _ => Classical.choice (inferInstance : Nonempty A),?_⟩
      intro g _
      exact map_ordinal (fun a => g • a) j
    · intro y hy
      obtain ⟨k,hk,rfl⟩ := (mem_ordinal y j).mp hy
      exact ih k hk

end

end WitnessedSeparation.Hereditary



namespace WitnessedSeparation.Grid

noncomputable section

open Classical Hereditary Counting HFCoding Interpretations

variable {n : ℕ} (b : Vertex n → Scalar)

variable {ι : Type} (bs : ι → Vertex n → Scalar) {s m : ℕ}

theorem program_domain_transitive (i : ι) :
    ∀ x ∈ programDomain bs (s := s) i, ∀ y, y ∈ x → y ∈ programDomain bs (s := s) i :=
  fun _ hx _ hy => hereditary_transitive hx hy

theorem program_mem_uniform : UniformDefinable (programHF bs (s := s)) m 2
    (fun _ v => (v 0).val ∈ (v 1).val) :=
  UniformDefinable.relation (S := programHF bs (s := s)) .mem 0 1

theorem program_set_uniform : UniformDefinable (programHF bs (s := s)) m 1
    (fun _ v => isSet (v 0).val = true) := by
  apply (UniformDefinable.relation (S := programHF bs (s := s)) .atom 0 0).neg.congr
  intro i v
  change (¬ isSet (v 0).val = false) ↔ _
  cases isSet (v 0).val <;> simp

theorem program_pure (hn : 1 ≤ n) (i : ι) (k : ℕ) : ordinal k ∈ programDomain bs (s := s) i := by
  let := atom_nonempty hn (bs i)
  exact ordinal_hereditary s k

end





end WitnessedSeparation.Grid



namespace WitnessedSeparation.Quantitative

noncomputable section

open Filter Asymptotics Topology

lemma const_little_rpow (c : ℝ) {r : ℝ} (hr : 0 < r) :
    (fun _ : ℝ => c) =o[atTop] (fun L => L^r) :=
  (isLittleO_const_id_atTop c).comp_tendsto (tendsto_rpow_atTop hr)

lemma power_little_power {a b : ℝ} (hab : a < b) :
    (fun L : ℝ => L^a) =o[atTop] (fun L => L^b) := by
  have h := (isBigO_refl (fun L : ℝ => L^a) atTop).mul_isLittleO (const_little_rpow 1 (sub_pos.mpr hab))
  apply h.congr' (by filter_upwards [] with L; simp)
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  rw [← Real.rpow_add hL]
  congr 1
  ring

lemma ceil_little {α : Type*} {l : Filter α} {f g : α → ℝ}
    (hf : ∀ᶠ x in l, 0 ≤ f x) (h : f =o[l] g) (h1 : (fun _ => (1:ℝ)) =o[l] g) :
    (fun x => (⌈f x⌉₊ : ℝ)) =o[l] g := by
  apply IsLittleO.of_bound
  intro c hc
  filter_upwards [hf,h.bound (show 0 < c/2 by linarith),h1.bound (show 0 < c/2 by linarith)] with x hx hh hconst
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  rw [Real.norm_of_nonneg hx] at hh
  norm_num at hconst
  have hb := Nat.ceil_lt_add_one hx
  simp only [Real.norm_eq_abs] at hh ⊢
  linarith

lemma log_volume_little (C q : ℝ) (hC : 0 < C) :
    (fun L : ℝ => q*Real.logb 3 (C*L^3)) =o[atTop] (fun L => L^((1:ℝ)/12)) := by
  have hc := const_little_rpow (Real.log C) (show 0 < (1:ℝ)/12 by norm_num)
  have hl := (isLittleO_log_rpow_atTop (show 0 < (1:ℝ)/12 by norm_num)).const_mul_left 3
  have h := ((hc.add hl).const_mul_left ((q:ℝ)/Real.log 3))
  apply h.congr' _ (Filter.Eventually.of_forall (fun _ => rfl))
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  simp only [Real.logb,Real.log_mul (ne_of_gt hC) (ne_of_gt (pow_pos hL 3)),Real.log_pow]
  ring

lemma radius_little (C q : ℝ) (hC : 0 < C) :
    (fun L : ℝ => (radius C q L : ℝ)) =o[atTop] (fun L => L^((7:ℝ)/6)) := by
  have hlog := log_volume_little C q hC
  have hsquare := hlog.pow (show 0 < 2 by omega)
  have hlin := (isBigO_refl (fun L : ℝ => L) atTop).mul_isLittleO hsquare
  have hraw : (fun L : ℝ => 2*L*(q*Real.logb 3 (C*L^3))^2) =o[atTop] (fun L => L^((7:ℝ)/6)) := by
    apply (hlin.const_mul_left 2).congr' (by filter_upwards [] with L; ring)
    filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
    calc
      L * (L ^ ((1:ℝ)/12)) ^ 2 = L^((1:ℝ)) * L^(((1:ℝ)/12)*2) := by
        rw [Real.rpow_one, Real.rpow_mul hL.le]; norm_num
      _ = L^((7:ℝ)/6) := by rw [← Real.rpow_add hL]; norm_num
  apply ceil_little _ hraw (const_little_rpow 1 (by norm_num))
  filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
  positivity

lemma radius_little_palette (C q : ℝ) (hC : 0 < C) :
    (fun L : ℝ => (radius C q L : ℝ)) =o[atTop] (fun L => L^((7:ℝ)/4)) :=
  (radius_little C q hC).trans (power_little_power (by norm_num))

lemma homogeneity_little (C q m c : ℝ) (hC : 0 < C) :
    (fun L : ℝ => 7*(m*(radius C q L:ℝ))+7*((6*(m*(radius C q L:ℝ)))/c)^((3:ℝ)/2)+1)
      =o[atTop] (fun L => L^((7:ℝ)/4)) := by
  have hlin := (radius_little_palette C q hC).const_mul_left (7*m)
  have hsr := (radius_little C q hC).const_mul_left (6*m/c)
  have hp := hsr.rpow (show 0 < (3:ℝ)/2 by norm_num)
    ((eventually_ge_atTop (0:ℝ)).mono (fun L hL => Real.rpow_nonneg hL _))
  have hp' : (fun L : ℝ => ((6*(m*(radius C q L:ℝ)))/c)^((3:ℝ)/2))
      =o[atTop] (fun L => L^((7:ℝ)/4)) := by
    apply hp.congr' (by filter_upwards [] with L; congr 1; ring)
    filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
    rw [← Real.rpow_mul hL]
    congr 1
    norm_num
  have h := (hlin.add (hp'.const_mul_left 7)).add (const_little_rpow 1 (by norm_num))
  apply h.congr_left
  intro L
  ring

lemma floor_big (a : ℝ) : (fun L : ℝ => (⌊L^a⌋₊:ℝ)) =O[atTop] (fun L => L^a) := by
  apply IsBigO.of_norm_eventuallyLE
  filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
  simp only [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact Nat.floor_le (Real.rpow_nonneg hL _)

lemma giant_little (c : ℝ) :
    (fun L : ℝ => ((12*(palette L:ℝ))/c)^((3:ℝ)/2)) =o[atTop] (fun L => L^3) := by
  have hb := (floor_big ((7:ℝ)/4)).const_mul_left (12/c)
  have hp := hb.rpow (show 0 ≤ (3:ℝ)/2 by norm_num)
    ((eventually_ge_atTop (0:ℝ)).mono (fun L hL => Real.rpow_nonneg hL _))
  have hp' : (fun L : ℝ => ((12*(palette L:ℝ))/c)^((3:ℝ)/2)) =O[atTop]
      (fun L => L^((21:ℝ)/8)) := by
    apply hp.congr' (by filter_upwards [] with L; simp only [palette]; congr 1; ring)
    filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
    rw [← Real.rpow_mul hL]
    congr 1
    norm_num
  have h := hp'.trans_isLittleO (power_little_power (a := (21:ℝ)/8) (b := 3) (by norm_num))
  exact h.congr_right (fun L => Real.rpow_natCast L 3)

theorem eventual_bounds (C q c : ℝ) (hC : 0 < C) (hc : 0 < c) (m : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      (max 4 (m+1):ℝ)*(radius C q L:ℝ) ≤ (palette L:ℝ) ∧
      7*((max 2 m:ℝ)*(radius C q L:ℝ))+
        7*((6*((max 2 m:ℝ)*(radius C q L:ℝ)))/c)^((3:ℝ)/2)+1 ≤ (palette L:ℝ) ∧
      ((12*(palette L:ℝ))/c)^((3:ℝ)/2) < L^3 := by
  have hw := ((radius_little_palette C q hC).const_mul_left (max 4 (m+1):ℝ)).bound
    (show 0 < (1:ℝ)/2 by norm_num)
  have hh := (homogeneity_little C q (max 2 m:ℝ) c hC).bound (show 0 < (1:ℝ)/2 by norm_num)
  have hg := (giant_little c).bound (show 0 < (1:ℝ)/2 by norm_num)
  filter_upwards [hw,hh,hg,eventually_gt_atTop (0:ℝ),
    (tendsto_rpow_atTop (show 0 < (7:ℝ)/4 by norm_num)).eventually_ge_atTop 2] with L hw hh hg hL hpow
  have hp : 0 ≤ L^((7:ℝ)/4) := Real.rpow_nonneg hL.le _
  have hs : 0 ≤ (radius C q L:ℝ) := Nat.cast_nonneg _
  have hfl := Nat.lt_floor_add_one (L^((7:ℝ)/4))
  have hn : 0 ≤ 7*((max 2 m:ℝ)*(radius C q L:ℝ))+
      7*((6*((max 2 m:ℝ)*(radius C q L:ℝ)))/c)^((3:ℝ)/2)+1 := by positivity
  rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg hp] at hw
  rw [Real.norm_of_nonneg hn,Real.norm_of_nonneg hp] at hh
  rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (pow_nonneg hL.le 3)] at hg
  change _ ≤ (⌊L^((7:ℝ)/4)⌋₊:ℝ) ∧ _ ≤ (⌊L^((7:ℝ)/4)⌋₊:ℝ) ∧ _
  refine ⟨by linarith,by linarith,?_⟩
  have hcube := pow_pos hL 3
  linarith

end





lemma timeExponent_ge_two (c d : ℕ) : 2 ≤ timeExponent c d := by unfold timeExponent; omega

lemma nat_le_power (N c : ℕ) (hN : 2 ≤ N) : c ≤ N^c := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [pow_succ]
    have hp : 1 ≤ N^c := Nat.one_le_pow _ _ (by omega)
    nlinarith

lemma polynomial_bounds (c d N : ℕ) (hN : 2 ≤ N) :
    2 ≤ N^timeExponent c d ∧ N ≤ N^timeExponent c d ∧
    c*(N+1)^d ≤ N^timeExponent c d ∧
    9*(N^timeExponent c d)^3 ≤ N^traceExponent c d := by
  have hpos : 1 ≤ N := by omega
  have hD := timeExponent_ge_two c d
  have hNB : N ≤ N^timeExponent c d := by
    simpa only [pow_one] using Nat.pow_le_pow_right hpos (show 1 ≤ timeExponent c d by omega)
  refine ⟨le_trans hN hNB,hNB,?_,?_⟩
  · calc
      c*(N+1)^d ≤ N^c*(N^2)^d := Nat.mul_le_mul (nat_le_power N c hN)
        (Nat.pow_le_pow_left (by nlinarith : N+1 ≤ N^2) d)
      _ = N^(c+2*d) := by rw [← pow_mul,← pow_add]
      _ ≤ N^timeExponent c d := Nat.pow_le_pow_right hpos (by unfold timeExponent; omega)
  · calc
      9*(N^timeExponent c d)^3 ≤ N^4*(N^timeExponent c d)^3 := by
        apply Nat.mul_le_mul_right
        have hh := Nat.pow_le_pow_left hN 4
        norm_num at hh
        omega
      _ = N^traceExponent c d := by
        rw [← pow_mul,← pow_add]
        unfold traceExponent
        congr 1
        omega

end WitnessedSeparation.Quantitative



end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_Machines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace WitnessedSeparation.Grid

noncomputable section

open Classical Hereditary Counting HFCoding Interpretations Quantitative Filter

lemma atomSizeConstant_pos : 0 < atomSizeConstant := by
  unfold atomSizeConstant localSizeBound
  positivity

theorem exists_numeric_box (q : ℕ) (hq : 0 < q) (m : ℕ) :
    ∃ n : ℕ, 1 ≤ n ∧
      let N : ℕ := atomSizeConstant*(n+1)^3
      let s : ℕ := ⌈2*(n+1:ℝ)*((q:ℝ)*Real.logb 3 N)^2⌉₊
      let M : ℕ := palette (n+1:ℝ)
      2 ≤ N ∧ 0 < s ∧ max 4 (m+1)*s ≤ M ∧
      (7:ℝ)*((max 2 m*s:ℕ):ℝ)+7*((6*((max 2 m*s:ℕ):ℝ))/boxConstant)^((3:ℝ)/2)+1 ≤ M ∧
      GiantBound n M := by
  have hC : 0 < (atomSizeConstant:ℝ) := by exact_mod_cast atomSizeConstant_pos
  have hev := eventual_bounds (atomSizeConstant:ℝ) (q:ℝ) boxConstant hC boxConstant_pos m
  have ht : Filter.Tendsto (fun n : ℕ => (n+1:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have he := ht.eventually hev
  obtain ⟨n,hn,hnum⟩ := ((eventually_ge_atTop (1:ℕ)).and he).exists
  refine ⟨n,hn,?_⟩
  dsimp only
  let N : ℕ := atomSizeConstant*(n+1)^3
  have hN : 2 ≤ N := by
    have hC' : 1 ≤ atomSizeConstant := atomSizeConstant_pos
    have hp : 2 ≤ (n+1)^3 := by
      have h := Nat.pow_le_pow_left (show 2 ≤ n+1 by omega) 3
      norm_num at h
      omega
    exact hp.trans (by simpa only [one_mul] using Nat.mul_le_mul_right ((n+1)^3) hC')
  have hlog : 0 < Real.logb 3 (N:ℝ) := Real.logb_pos (by norm_num) (by exact_mod_cast hN)
  have hs : 0 < ⌈2*(n+1:ℝ)*((q:ℝ)*Real.logb 3 N)^2⌉₊ := by
    apply Nat.ceil_pos.mpr
    have hq' : 0 < (q:ℝ) := by exact_mod_cast hq
    positivity
  have hrad : radius (atomSizeConstant:ℝ) (q:ℝ) (n+1:ℝ) =
      ⌈2*(n+1:ℝ)*((q:ℝ)*Real.logb 3 N)^2⌉₊ := by
    simp only [radius,N,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one]
  rw [hrad] at hnum
  refine ⟨hN,hs,?_,?_,?_⟩
  · exact_mod_cast hnum.1
  · simpa only [N,Nat.cast_mul, Nat.cast_max, Nat.cast_ofNat] using hnum.2.1
  · simpa only [GiantBound,Nat.cast_pow,Nat.cast_add,Nat.cast_one] using hnum.2.2

end

end WitnessedSeparation.Grid



end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_TraceGraphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace WitnessedSeparation.Grid

noncomputable section

open Classical Hereditary Counting HFCoding Operational Finset

variable {n : ℕ}
  (b : Vertex n → Scalar)

variable {ι : Type} (bs : ι → Vertex n → Scalar) {s m : ℕ}

lemma program_atom_mem (hs : 0 < s) (i : ι) (a : Atom (bs i)) :
    atom a ∈ programDomain bs (s := s) i := by
  apply hereditary_iff.mpr
  constructor
  · refine ⟨fun _ => a,?_⟩
    intro g hg
    rw [smul_atom,hg ⟨0,hs⟩]
  · intro y hy
    have hh : y ∈ (∅ : Finset (HF (Atom (bs i)))) := hy
    exact (notMem_empty _ hh).elim

lemma op_input_uniform (r : Symbol) :
    UniformDefinable (programHF bs (s := s)) m 2
      (fun i v => inputRelation (atomInput (bs i)).rel r (v 0).val (v 1).val) := by
  apply (UniformDefinable.relation (S := programHF bs) (.base (.input r)) 0 1).congr
  intro i v
  change (∃ a b, (v 0).val = atom a ∧ (v 1).val = atom b ∧ AtomRelation (bs i) r a b) ↔ _
  simp only [inputRelation,atomInput,decide_eq_true_eq]

end





end WitnessedSeparation.Grid



namespace WitnessedSeparation.PolynomialCost

open Finset

lemma eval_bound (p : Polynomial ℕ) : ∃ c d : ℕ, ∀ K, p.eval K ≤ c*(K+1)^d := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr =>
    obtain ⟨c,d,hp⟩ := hp
    obtain ⟨e,f,hr⟩ := hr
    refine ⟨c+e,d+f,fun K => ?_⟩
    rw [Polynomial.eval_add]
    have h1 : (K+1)^d ≤ (K+1)^(d+f) := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : (K+1)^f ≤ (K+1)^(d+f) := Nat.pow_le_pow_right (by omega) (by omega)
    calc
      p.eval K + r.eval K ≤ c*(K+1)^d + e*(K+1)^f := add_le_add (hp K) (hr K)
      _ ≤ c*(K+1)^(d+f)+e*(K+1)^(d+f) := add_le_add (Nat.mul_le_mul_left _ h1) (Nat.mul_le_mul_left _ h2)
      _ = _ := by ring
  | monomial n a =>
    refine ⟨a,n,fun K => ?_⟩
    rw [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left a (Nat.pow_le_pow_left (by omega) n)

end WitnessedSeparation.PolynomialCost



end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_LowerBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section



namespace WitnessedSeparation.PolynomialCost

lemma eval_mono (p : Polynomial ℕ) {a b : ℕ} (hab : a ≤ b) : p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using add_le_add hp hq
  | monomial n c => simpa only [Polynomial.eval_monomial] using Nat.mul_le_mul_left c (Nat.pow_le_pow_left hab n)

end WitnessedSeparation.PolynomialCost



namespace WitnessedSeparation.Grid


open Classical Hereditary Counting HFCoding Operational Quantitative Finset

variable {n : ℕ}

lemma atom_card_independent (hn : 1 ≤ n) (b b' : Vertex n → Scalar) :
    Fintype.card (Atom b) = Fintype.card (Atom b') := by
  have hv (v : Vertex n) : ∃ t : Edge n → Scalar, boundary t v = b' v - b v := by
    obtain ⟨e,he⟩ := exists_head_or_tail hn v
    rcases he with he | he
    · refine ⟨Pi.single e (b' v-b v),?_⟩
      rw [boundary_single]
      subst v
      simp [head_ne_tail]
    · refine ⟨Pi.single e (-(b' v-b v)),?_⟩
      rw [boundary_single]
      subst v
      simp [Ne.symm (head_ne_tail e)]
  choose tv htv using hv
  exact Fintype.card_congr (blockShiftEquiv (fun _ _ => 0) tv htv)


end WitnessedSeparation.Grid



end

end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_ChoiceTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

variable {A : Type} [Fintype A]

mutual
  theorem Term.eval_traced (S : Input A) (p : Polynomial ℝ) {n : ℕ}
      (t : Term n) (ht : t.wscCount = 0) (env : Fin n → HF A) :
      t.eval S p env = some (t.traced S (resource p (Fintype.card A)) env).1 := by
    cases t with
    | var j => rfl
    | empty => rfl
    | atoms =>
      simp only [Term.eval,Term.traced]
    | pair a b =>
      have h := Nat.add_eq_zero_iff.mp ht
      simp only [Term.eval,Term.traced,lift₂,a.eval_traced S p h.1 env,
        b.eval_traced S p h.2 env,Option.bind_some,Option.map_some]
    | union a => simp only [Term.eval,Term.traced,a.eval_traced S p ht env,Option.map_some]
    | unique a => simp only [Term.eval,Term.traced,a.eval_traced S p ht env,Option.map_some]
    | card a => simp only [Term.eval,Term.traced,a.eval_traced S p ht env,Option.map_some]
    | comprehend body range guard =>
      have h := Nat.add_eq_zero_iff.mp ht
      have h' := Nat.add_eq_zero_iff.mp h.1
      simp only [Term.eval,range.eval_traced S p h'.2 env,Option.bind_some]
      have hg : ∀ x : HF A, guard.eval S p (Fin.cons x env) =
          some (guard.traced S (resource p (Fintype.card A)) (Fin.cons x env)).1 :=
        fun x => guard.eval_traced S p h.2 _
      have hb : ∀ x : HF A, body.eval S p (Fin.cons x env) =
          some (body.traced S (resource p (Fintype.card A)) (Fin.cons x env)).1 :=
        fun x => body.eval_traced S p h'.1 _
      simp only [collect,hg,hb,Option.isSome_some,
        implies_true,and_self,ite_true,Option.getD_some,Term.traced,Option.some.injEq]
    | iterate step =>
      exact iterationLoop_traced _ _ _
        (fun x => step.eval_traced S p ht (Fin.cons x env)) _ _
  theorem Formula.eval_traced (S : Input A) (p : Polynomial ℝ) {n : ℕ}
      (f : Formula n) (hf : f.wscCount = 0) (env : Fin n → HF A) :
      f.eval S p env = some (f.traced S (resource p (Fintype.card A)) env).1 := by
    cases f with
    | equal a b =>
      have h := Nat.add_eq_zero_iff.mp hf
      simp only [Formula.eval,Formula.traced,lift₂,a.eval_traced S p h.1 env,
        b.eval_traced S p h.2 env,Option.bind_some,Option.map_some]
    | input r a b =>
      have h := Nat.add_eq_zero_iff.mp hf
      simp only [Formula.eval,Formula.traced,lift₂,a.eval_traced S p h.1 env,
        b.eval_traced S p h.2 env,Option.bind_some,Option.map_some]
    | neg a => simp only [Formula.eval,Formula.traced,a.eval_traced S p hf env,Option.map_some]
    | and a b =>
      have h := Nat.add_eq_zero_iff.mp hf
      simp only [Formula.eval,Formula.traced,lift₂,a.eval_traced S p h.1 env,
        b.eval_traced S p h.2 env,Option.bind_some,Option.map_some]
    | or a b =>
      have h := Nat.add_eq_zero_iff.mp hf
      simp only [Formula.eval,Formula.traced,lift₂,a.eval_traced S p h.1 env,
        b.eval_traced S p h.2 env,Option.bind_some,Option.map_some]
    | wsc step choice witness output => simp only [Formula.wscCount] at hf; omega
end

end

end WitnessedChoice.BGS

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

variable {A : Type}

variable [Fintype A]

mutual
  lemma Term.traced_closed (S : Input A) (p : ℕ) {n : ℕ} (t : Term n)
      (env : Fin n → HF A) : ClosedTrace (t.traced S p env).2 := by
    cases t with
    | var j => exact closedTrace_closure _
    | empty => exact closedTrace_closure _
    | atoms => exact closedTrace_closure _
    | pair a b =>
      exact closedTrace_insert (closedTrace_union (a.traced_closed S p env)
        (b.traced_closed S p env)) _ ((Term.pair a b).traced_closure S p env)
    | union a =>
      exact closedTrace_insert (a.traced_closed S p env) _ ((Term.union a).traced_closure S p env)
    | unique a =>
      exact closedTrace_insert (a.traced_closed S p env) _ ((Term.unique a).traced_closure S p env)
    | card a => exact closedTrace_union (closedTrace_closure _) (a.traced_closed S p env)
    | comprehend body range guard =>
      apply closedTrace_insert _ _ ((Term.comprehend body range guard).traced_closure S p env)
      exact closedTrace_union (closedTrace_union (range.traced_closed S p env)
        (closedTrace_biUnion _ _ (fun x _ => guard.traced_closed S p (Fin.cons x env))))
        (closedTrace_biUnion _ _ (fun x _ => body.traced_closed S p (Fin.cons x env)))
    | iterate step =>
      exact tracedLoop_closed p _ (fun x => step.traced_closed S p (Fin.cons x env)) _ _
  lemma Formula.traced_closed (S : Input A) (p : ℕ) {n : ℕ} (f : Formula n)
      (env : Fin n → HF A) : ClosedTrace (f.traced S p env).2 := by
    cases f with
    | equal a b | input r a b => exact closedTrace_union (a.traced_closed S p env) (b.traced_closed S p env)
    | neg a => exact a.traced_closed S p env
    | and a b | or a b => exact closedTrace_union (a.traced_closed S p env) (b.traced_closed S p env)
    | wsc step choice witness output => intro x hx; exact False.elim (Finset.notMem_empty _ hx)
end

end

end WitnessedChoice.BGS

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary Finset

variable {A : Type}

variable [Fintype A]

mutual
  lemma Term.traced_card_le (S : Input A) (p : ℕ) {n : ℕ} (t : Term n)
      (env : Fin n → HF A) (K : ℕ) (hK : tracePotential p env ≤ K) :
      (t.traced S p env).2.card ≤ t.traceBound.eval K := by
    cases t with
    | var j =>
      simpa only [Term.traced,Term.traceBound,Polynomial.eval_X] using (tracePotential_var p env j).trans hK
    | empty =>
      simp only [Term.traced,closure_emptyHF,card_singleton,Term.traceBound,Polynomial.eval_one,le_refl]
    | atoms =>
      have hk : Fintype.card A+1 ≤ K := by unfold tracePotential at hK; omega
      simpa only [Term.traced,Term.traceBound,Polynomial.eval_X] using card_closure_atoms.trans hk
    | pair a b =>
      have ha := a.traced_card_le S p env K hK
      have hb := b.traced_card_le S p env K hK
      have hh := (card_insert_le (double (a.traced S p env).1 (b.traced S p env).1)
        ((a.traced S p env).2 ∪ (b.traced S p env).2)).trans
        (Nat.add_le_add_right (card_union_le _ _) 1)
      simp only [Term.traced,Term.traceBound,Polynomial.eval_add,Polynomial.eval_one]
      omega
    | union a | unique a =>
      have ha := a.traced_card_le S p env K hK
      have hh := card_insert_le (s := (a.traced S p env).2)
      simp only [Term.traced,Term.traceBound,Polynomial.eval_add,Polynomial.eval_one]
      exact (hh _).trans (by omega)
    | card a =>
      have ha := a.traced_card_le S p env K hK
      have hc : (closure (cardHF (a.traced S p env).1)).card ≤ a.traceBound.eval K+1 := by
        rw [cardHF,card_closure_ordinal]
        exact Nat.add_le_add_right ((card_le_card ((elements_subset_closure _).trans
          (a.traced_closure S p env))).trans ha) 1
      have hh := (card_union_le _ _).trans (add_le_add hc ha)
      simp only [Term.traced,Term.traceBound,Polynomial.eval_add,Polynomial.eval_one,
        Polynomial.eval_mul,Polynomial.eval_ofNat]
      exact hh.trans (by omega)
    | comprehend body range guard =>
      have hr := range.traced_card_le S p env K hK
      have hc : (elements (range.traced S p env).1).card ≤ range.traceBound.eval K :=
        (card_le_card ((elements_subset_closure _).trans (range.traced_closure S p env))).trans hr
      have hen (x) (hx : x ∈ elements (range.traced S p env).1) :
          tracePotential p (Fin.cons x env) ≤ K+range.traceBound.eval K := by
        rw [tracePotential_cons]
        exact add_le_add hK ((card_le_card ((closure_member_subset hx).trans
          (range.traced_closure S p env))).trans hr)
      let E := elements (range.traced S p env).1
      let D := E.filter (fun x => (guard.traced S p (Fin.cons x env)).1 = true)
      have hg : (E.biUnion fun x => (guard.traced S p (Fin.cons x env)).2).card ≤
          range.traceBound.eval K*guard.traceBound.eval (K+range.traceBound.eval K) := by
        apply card_biUnion_le.trans
        apply (sum_le_card_nsmul E _ _ (fun x hx => guard.traced_card_le S p _ _ (hen x hx))).trans
        simpa only [nsmul_eq_mul,Nat.cast_id] using Nat.mul_le_mul_right _ hc
      have hb : (D.biUnion fun x => (body.traced S p (Fin.cons x env)).2).card ≤
          range.traceBound.eval K*body.traceBound.eval (K+range.traceBound.eval K) := by
        apply card_biUnion_le.trans
        apply (sum_le_card_nsmul D _ _ (fun x hx => body.traced_card_le S p _ _
          (hen x (mem_filter.mp hx).1))).trans
        simpa only [nsmul_eq_mul,Nat.cast_id] using
          Nat.mul_le_mul_right _ ((card_le_card (filter_subset _ _)).trans hc)
      have hh := (card_insert_le (s := (range.traced S p env).2 ∪
        (E.biUnion fun x => (guard.traced S p (Fin.cons x env)).2) ∪
        (D.biUnion fun x => (body.traced S p (Fin.cons x env)).2))
        (ofFinset (D.image fun x => (body.traced S p (Fin.cons x env)).1))).trans
        (Nat.add_le_add_right ((card_union_le _ _).trans
          (add_le_add ((card_union_le _ _).trans (add_le_add hr hg)) hb)) 1)
      simp only [Term.traced,Term.traceBound,Polynomial.eval_add,Polynomial.eval_one,
        Polynomial.eval_mul,Polynomial.eval_comp,Polynomial.eval_X]
      change (insert _ ((range.traced S p env).2 ∪ _ ∪ _)).card ≤ _ at hh
      exact hh.trans (by ring_nf; omega)
    | iterate step =>
      have hk : p+1 ≤ K := by unfold tracePotential at hK; omega
      have hb := tracedLoop_card p (fun x => step.traced S p (Fin.cons x env))
        (step.traceBound.eval (2*K)) (fun x hx => step.traced_card_le S p _ _ (by
          rw [tracePotential_cons]
          have hc := (closure_card_le_TC x).trans (Nat.add_le_add_right hx 1)
          omega)) (p+1) emptyHF
      simp only [Term.traced,Term.traceBound,Polynomial.eval_add,Polynomial.eval_one,
        Polynomial.eval_mul,Polynomial.eval_comp,Polynomial.eval_X,Polynomial.eval_ofNat]
      exact hb.trans (by nlinarith [Nat.mul_le_mul_right (step.traceBound.eval (2*K)) hk])
  lemma Formula.traced_card_le (S : Input A) (p : ℕ) {n : ℕ} (f : Formula n)
      (env : Fin n → HF A) (K : ℕ) (hK : tracePotential p env ≤ K) :
      (f.traced S p env).2.card ≤ f.traceBound.eval K := by
    cases f with
    | equal a b | input r a b =>
      simp only [Formula.traced,Formula.traceBound,Polynomial.eval_add]
      exact (card_union_le _ _).trans (add_le_add (a.traced_card_le S p env K hK)
        (b.traced_card_le S p env K hK))
    | neg a => exact a.traced_card_le S p env K hK
    | and a b | or a b =>
      simp only [Formula.traced,Formula.traceBound,Polynomial.eval_add]
      exact (card_union_le _ _).trans (add_le_add (a.traced_card_le S p env K hK)
        (b.traced_card_le S p env K hK))
    | wsc step choice witness output => simp only [Formula.traced,Formula.traceBound,Polynomial.eval_zero,card_empty,le_refl]
end

end

end WitnessedChoice.BGS

end

end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_TermGraphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary WitnessedSeparation.HFCoding

variable {A : Type}

variable [Fintype A]

mutual
  lemma Term.graph_complete (d : Set (HF A)) (S : Input A) (p K : ℕ)
      (hd : ∀ x ∈ d, ∀ y, y ∈ x → y ∈ d) (hempty : emptyHF ∈ d) {n : ℕ} (t : Term n) (hzero : t.wscCount = 0)
      (z : Domain d) (env : Fin n → Domain d)
      (ht : AdmissibleTrace d K (t.traced S p (fun j => (env j).val)).2)
      (hz : z.val = (t.traced S p (fun j => (env j).val)).1) : t.Graph d S p K z env := by
    cases t with
    | var j => exact Subtype.ext hz
    | empty => exact hz
    | atoms => exact hz
    | pair a b =>
      have h := Nat.add_eq_zero_iff.mp hzero
      have ha := ht.mono (Finset.subset_union_left.trans (Finset.subset_insert _ _))
      have hb := ht.mono (Finset.subset_union_right.trans (Finset.subset_insert _ _))
      let x : Domain d := ⟨(a.traced S p (fun j => (env j).val)).1,(ha _ (a.traced_self S p _)).1⟩
      let y : Domain d := ⟨(b.traced S p (fun j => (env j).val)).1,(hb _ (b.traced_self S p _)).1⟩
      exact ⟨x,y,a.graph_complete d S p K hd hempty h.1 x env ha rfl,
        b.graph_complete d S p K hd hempty h.2 y env hb rfl,hz⟩
    | union a | unique a =>
      have ha := ht.mono (Finset.subset_insert _ _)
      let x : Domain d := ⟨(a.traced S p (fun j => (env j).val)).1,(ha _ (a.traced_self S p _)).1⟩
      exact ⟨x,a.graph_complete d S p K hd hempty hzero x env ha rfl,hz⟩
    | card a =>
      have ha := ht.mono Finset.subset_union_right
      let x : Domain d := ⟨(a.traced S p (fun j => (env j).val)).1,(ha _ (a.traced_self S p _)).1⟩
      exact ⟨x,a.graph_complete d S p K hd hempty hzero x env ha rfl,
        (ha _ (a.traced_self S p _)).2,hz⟩
    | comprehend body range guard =>
      have h := Nat.add_eq_zero_iff.mp hzero
      have h' := Nat.add_eq_zero_iff.mp h.1
      have hr := ht.mono (Finset.subset_union_left.trans
        (Finset.subset_union_left.trans (Finset.subset_insert _ _)))
      let r : Domain d := ⟨(range.traced S p (fun j => (env j).val)).1,
        (hr _ (range.traced_self S p _)).1⟩
      have hg (x : Domain d) (hx : x.val ∈ r.val) :
          AdmissibleTrace d K (guard.traced S p (fun j => ((Fin.cons x env : Fin (_+1) → Domain d) j).val)).2 := by
        rw [domain_cons_val]
        apply ht.mono
        intro y hy
        exact Finset.mem_insert_of_mem (Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨x.val,hx,hy⟩)))
      have hb (x : Domain d) (hx : x.val ∈ r.val)
          (hxg : (guard.traced S p (fun j => ((Fin.cons x env : Fin (_+1) → Domain d) j).val)).1 = true) :
          AdmissibleTrace d K (body.traced S p (fun j => ((Fin.cons x env : Fin (_+1) → Domain d) j).val)).2 := by
        rw [domain_cons_val] at hxg ⊢
        apply ht.mono
        intro y hy
        exact Finset.mem_insert_of_mem (Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨x.val,Finset.mem_filter.mpr ⟨hx,hxg⟩,hy⟩))
      refine ⟨r,range.graph_complete d S p K hd hempty h'.2 r env hr rfl,?_,?_,?_⟩
      · intro x hx
        refine ⟨(guard.traced S p (fun j => ((Fin.cons x env : Fin (_+1) → Domain d) j).val)).1,
          guard.graph_complete d S p K hd hempty h.2 _ _ (hg x hx) rfl,?_⟩
        intro hxg
        let y : Domain d := ⟨(body.traced S p (fun j => ((Fin.cons x env : Fin (_+1) → Domain d) j).val)).1,
          ((hb x hx hxg) _ (body.traced_self S p _)).1⟩
        exact ⟨y,body.graph_complete d S p K hd hempty h'.1 y _ (hb x hx hxg) rfl⟩
      · rw [hz]; exact isSet_ofFinset _
      · intro y
        rw [hz]
        change y.val ∈ ofFinset _ ↔ _
        simp only [mem_ofFinset,Finset.mem_image,Finset.mem_filter]
        constructor
        · rintro ⟨x,⟨hx,hxg⟩,hy⟩
          have hxd : x ∈ d := (hr x (range.traced_closure S p _ (elements_subset_closure _ hx))).1
          let xx : Domain d := ⟨x,hxd⟩
          have hxg' : (guard.traced S p (fun j => ((Fin.cons xx env : Fin (_+1) → Domain d) j).val)).1 = true := by
            simpa only [domain_cons_val] using hxg
          refine ⟨xx,hx,guard.graph_complete d S p K hd hempty h.2 true _ (hg xx hx) hxg'.symm,?_⟩
          apply body.graph_complete d S p K hd hempty h'.1 y _ (hb xx hx hxg')
          simpa only [domain_cons_val] using hy.symm
        · rintro ⟨x,hx,hxg,hy⟩
          have hgt := guard.graph_sound d S p K hd true (Fin.cons x env) hxg
          have hbt := body.graph_sound d S p K hd y (Fin.cons x env) hy
          simp only [domain_cons_val] at hgt hbt
          exact ⟨x.val,⟨hx,hgt.symm⟩,hbt.symm⟩
    | iterate step =>
      let x : Domain d := ⟨emptyHF,hempty⟩
      refine ⟨x,rfl,LoopGraph.complete p K (step.Graph d S p K)
        (fun y => step.traced S p (Fin.cons y (fun j => (env j).val))) env
        (fun y => step.traced_self S p _) ?_ (p+1) z x ht hz⟩
      intro a b ha hb
      apply step.graph_complete d S p K hd hempty hzero b (Fin.cons a env)
      · simpa only [domain_cons_val] using ha
      · simpa only [domain_cons_val] using hb
  termination_by sizeOf t
  decreasing_by all_goals subst_vars; simp_wf <;> omega
  lemma Formula.graph_complete (d : Set (HF A)) (S : Input A) (p K : ℕ)
      (hd : ∀ x ∈ d, ∀ y, y ∈ x → y ∈ d) (hempty : emptyHF ∈ d) {n : ℕ} (f : Formula n) (hzero : f.wscCount = 0)
      (v : Bool) (env : Fin n → Domain d)
      (ht : AdmissibleTrace d K (f.traced S p (fun j => (env j).val)).2)
      (hv : v = (f.traced S p (fun j => (env j).val)).1) : f.Graph d S p K v env := by
    cases f with
    | equal a b | input r a b =>
      have h := Nat.add_eq_zero_iff.mp hzero
      have ha := ht.mono Finset.subset_union_left
      have hb := ht.mono Finset.subset_union_right
      let x : Domain d := ⟨(a.traced S p (fun j => (env j).val)).1,(ha _ (a.traced_self S p _)).1⟩
      let y : Domain d := ⟨(b.traced S p (fun j => (env j).val)).1,(hb _ (b.traced_self S p _)).1⟩
      exact ⟨x,y,a.graph_complete d S p K hd hempty h.1 x env ha rfl,
        b.graph_complete d S p K hd hempty h.2 y env hb rfl,hv⟩
    | neg a => exact ⟨_,a.graph_complete d S p K hd hempty hzero _ env ht rfl,hv⟩
    | and a b | or a b =>
      have h := Nat.add_eq_zero_iff.mp hzero
      exact ⟨_,_,a.graph_complete d S p K hd hempty h.1 _ env (ht.mono Finset.subset_union_left) rfl,
        b.graph_complete d S p K hd hempty h.2 _ env (ht.mono Finset.subset_union_right) rfl,hv⟩
    | wsc step choice witness output => simp only [Formula.wscCount] at hzero; omega
  termination_by sizeOf f
  decreasing_by all_goals subst_vars; simp_wf <;> omega
end

end

end WitnessedChoice.BGS

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary WitnessedSeparation.Counting WitnessedSeparation.HFCoding

variable {ι R : Type} {A : ι → Type} [∀ i, Fintype (A i)]

variable (d : ∀ i, Set (HF (A i))) (T : ∀ i, Counting.Structure R (Domain (d i))) {m : ℕ}

variable (hd : ∀ i, ∀ x ∈ d i, ∀ y, y ∈ x → y ∈ d i)

variable (hp : ∀ i k, ordinal (A := A i) k ∈ d i)

variable (ha : ∀ i a, atom a ∈ d i)

variable (hmem : UniformDefinable T m 2 (fun _ v => (v 0).val ∈ (v 1).val))

variable (hset : UniformDefinable T m 1 (fun _ v => isSet (v 0).val = true))

variable (S : ∀ i, Input (A i))

variable (hinput : ∀ r, UniformDefinable T m 2
    (fun i v => Operational.inputRelation (S i).rel r (v 0).val (v 1).val))

mutual
  lemma Term.uniform_graph (d : ∀ i, Set (HF (A i))) (T : ∀ i, Counting.Structure R (Domain (d i)))
      (hd : ∀ i, ∀ x ∈ d i, ∀ y, y ∈ x → y ∈ d i)
      (hp : ∀ i k, ordinal (A := A i) k ∈ d i)
      (ha : ∀ i a, atom a ∈ d i)
      (hmem : UniformDefinable T m 2 (fun _ v => (v 0).val ∈ (v 1).val))
      (hset : UniformDefinable T m 1 (fun _ v => isSet (v 0).val = true))
      (S : ∀ i, Input (A i))
      (hinput : ∀ r, UniformDefinable T m 2
        (fun i v => Operational.inputRelation (S i).rel r (v 0).val (v 1).val)) (p K : ℕ) {n : ℕ} (t : Term n) (hm : t.graphWidth ≤ m) :
      UniformDefinable T m (n+1) (fun i v => t.Graph (d i) (S i) p K (v 0) (Fin.tail v)) := by
    cases t with
    | var j => exact UniformDefinable.equal 0 j.succ
    | empty =>
      simp only [Term.graphWidth] at hm
      exact (HFCoding.uniform_ordinal T hmem hset (by omega) hd hp 0).reindex ![0]
    | atoms =>
      simp only [Term.graphWidth] at hm
      apply ((Operational.uniform_atoms d T hd ha hmem hset (by omega)).reindex ![0]).congr
      intro i v
      simp only [Term.Graph,atomsHF_eq_operational,Function.comp_apply]
      rfl
    | pair a b =>
      simp only [Term.graphWidth] at hm
      exact UniformDefinable.compose_binary
        (a.uniform_graph d T hd hp ha hmem hset S hinput p K (by omega))
        (b.uniform_graph d T hd hp ha hmem hset S hinput p K (by omega))
        (Operational.uniform_double_value d T hd hmem hset (by omega)) (by omega)
    | union a =>
      simp only [Term.graphWidth] at hm
      have hh := UniformDefinable.compose_unary
        (a.uniform_graph d T hd hp ha hmem hset S hinput p K (by omega))
        (Operational.uniform_union d T hd hmem hset (by omega)) (by omega : n+1 < m)
      apply hh.congr
      intro i v
      simp only [Term.Graph,unionHF_eq_operational,Fin.cons_zero,Fin.tail_cons]
      rfl
    | unique a =>
      simp only [Term.graphWidth] at hm
      exact UniformDefinable.compose_unary
        (a.uniform_graph d T hd hp ha hmem hset S hinput p K (by omega))
        (Operational.uniform_unique d T hd hp hmem hset (by omega)) (by omega)
    | card a =>
      simp only [Term.graphWidth] at hm
      exact UniformDefinable.compose_unary
        (a.uniform_graph d T hd hp ha hmem hset S hinput p K (by omega))
        (Operational.uniform_card d T hd hp hmem hset (by omega) K) (by omega)
    | comprehend body range guard =>
      simp only [Term.graphWidth] at hm
      exact uniform_BGS_comprehension d T hmem hset
        (range.uniform_graph d T hd hp ha hmem hset S hinput p K (by omega))
        (fun b => guard.uniform_graph d T hd hp ha hmem hset S hinput p K b (by omega))
        (body.uniform_graph d T hd hp ha hmem hset S hinput p K (by omega)) (by omega)
    | iterate step =>
      simp only [Term.graphWidth] at hm
      have hs := step.uniform_graph d T hd hp ha hmem hset S hinput p K (by omega)
      have hc := uniform_TC_bound d T hd hmem (by omega) p
      have he : UniformDefinable T m 1 (fun _ v => (v 0).val = emptyHF) :=
        HFCoding.uniform_ordinal T hmem hset (by omega) hd hp 0
      have hl := (LoopGraph.uniform d T p (fun i => step.Graph (d i) (S i) p K)
        hs hc he (by omega : n+2 < m) (p+1)).reindex
          (Fin.cons 1 (Fin.cons 0 (fun j => j.succ.succ)) : Fin (n+2) → Fin (n+2))
      apply (((he.reindex (![0] : Fin 1 → Fin (n+2))).and hl).ex (by omega)).congr
      intro i v
      simp only [Term.Graph,Fin.comp_cons,Fin.cons_zero,Fin.tail_cons,Function.comp_apply]
      rfl
  termination_by sizeOf t
  decreasing_by all_goals subst_vars; simp_wf <;> omega
  lemma Formula.uniform_graph (d : ∀ i, Set (HF (A i))) (T : ∀ i, Counting.Structure R (Domain (d i)))
      (hd : ∀ i, ∀ x ∈ d i, ∀ y, y ∈ x → y ∈ d i)
      (hp : ∀ i k, ordinal (A := A i) k ∈ d i)
      (ha : ∀ i a, atom a ∈ d i)
      (hmem : UniformDefinable T m 2 (fun _ v => (v 0).val ∈ (v 1).val))
      (hset : UniformDefinable T m 1 (fun _ v => isSet (v 0).val = true))
      (S : ∀ i, Input (A i))
      (hinput : ∀ r, UniformDefinable T m 2
        (fun i v => Operational.inputRelation (S i).rel r (v 0).val (v 1).val)) (p K : ℕ) {n : ℕ} (f : Formula n) (b : Bool)
      (hm : f.graphWidth ≤ m) :
      UniformDefinable T m n (fun i v => f.Graph (d i) (S i) p K b v) := by
    cases f with
    | equal a c =>
      simp only [Formula.graphWidth] at hm
      have he : UniformDefinable T m 2 (fun _ v => (v 0).val = (v 1).val) :=
        (UniformDefinable.equal 0 1).congr (fun _ _ => Subtype.ext_iff)
      apply (uniform_formula_binary
        (a.uniform_graph d T hd hp ha hmem hset S hinput p K (by omega))
        (c.uniform_graph d T hd hp ha hmem hset S hinput p K (by omega))
        (uniform_decide he b) (by omega : n+1 < m)).congr
      intro i v
      simp only [Formula.Graph,Fin.cons_zero,Fin.tail_cons]
      apply exists_congr; intro x
      apply exists_congr; intro y
      simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
      apply and_congr_right; intro _
      apply and_congr_right; intro _
      apply Iff.of_eq
      apply congrArg (fun z : Bool => b = z)
      exact decide_eq_decide.mpr Iff.rfl
    | input r a c =>
      simp only [Formula.graphWidth] at hm
      exact uniform_formula_binary
        (a.uniform_graph d T hd hp ha hmem hset S hinput p K (by omega))
        (c.uniform_graph d T hd hp ha hmem hset S hinput p K (by omega))
        (uniform_decide (hinput r) b) (by omega)
    | neg a =>
      simp only [Formula.graphWidth] at hm
      exact uniform_exists_finite (fun c : Bool =>
        (a.uniform_graph d T hd hp ha hmem hset S hinput p K c (by omega)).and
          (uniform_const (b = !c)))
    | and a c =>
      simp only [Formula.graphWidth] at hm
      exact uniform_exists_finite (fun x : Bool => uniform_exists_finite (fun y : Bool =>
        (a.uniform_graph d T hd hp ha hmem hset S hinput p K x (by omega)).and
          ((c.uniform_graph d T hd hp ha hmem hset S hinput p K y (by omega)).and
            (uniform_const (b = (x && y))))))
    | or a c =>
      simp only [Formula.graphWidth] at hm
      exact uniform_exists_finite (fun x : Bool => uniform_exists_finite (fun y : Bool =>
        (a.uniform_graph d T hd hp ha hmem hset S hinput p K x (by omega)).and
          ((c.uniform_graph d T hd hp ha hmem hset S hinput p K y (by omega)).and
            (uniform_const (b = (x || y))))))
    | wsc step choice witness output => exact UniformDefinable.falsum
  termination_by sizeOf f
  decreasing_by all_goals subst_vars; simp_wf <;> omega
end

end

end WitnessedChoice.BGS

end

section

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary Finset

open WitnessedSeparation.Operational (lift lift_elements lift_ofFinset lift_empty lift_double)

variable {A B : Type}

variable [Fintype A] [Fintype B]

mutual
  theorem Term.traced_transport (e : A ≃ B) (S : Input A) (T : Input B)
      (h : ∀ r a b, T.rel r (e a) (e b) = S.rel r a b) (p : ℕ)
      {n : ℕ} (t : Term n) (env : Fin n → HF A) :
      t.traced T p (fun j => lift e (env j)) =
        (lift e (t.traced S p env).1,(t.traced S p env).2.image (lift e)) := by
    cases t with
    | var j => exact Prod.ext rfl (lift_closureHF e _)
    | empty => simp only [Term.traced,lift_emptyHF,closure_emptyHF,image_singleton]
    | atoms => simp only [Term.traced,← lift_atomsHF e,lift_closureHF]
    | pair a b =>
      simp only [Term.traced,a.traced_transport e S T h p env,b.traced_transport e S T h p env,
        image_insert,image_union,lift_double]
    | union a =>
      simp only [Term.traced,a.traced_transport e S T h p env,image_insert,lift_unionHF]
    | unique a =>
      simp only [Term.traced,a.traced_transport e S T h p env,image_insert,lift_uniqueHF]
    | card a =>
      simp only [Term.traced,a.traced_transport e S T h p env,image_union,← lift_cardHF,lift_closureHF]
    | comprehend body range guard =>
      have hr := range.traced_transport e S T h p env
      have hg (x : HF A) := guard.traced_transport e S T h p (Fin.cons x env)
      have hb (x : HF A) := body.traced_transport e S T h p (Fin.cons x env)
      simp only [lift_cons] at hg hb
      have hs := selected_transport e (range.traced S p env).1
        (fun x => (guard.traced S p (Fin.cons x env)).1)
        (fun x => (guard.traced T p (Fin.cons x (fun j => lift e (env j)))).1)
        (fun x => congrArg Prod.fst (hg x))
      simp only [Term.traced,hr]
      rw [hs]
      simp only [image_image,Function.comp_def,hb,lift_ofFinset,
        lift_elements,biUnion_image,image_insert,image_union,image_biUnion,hg]
      congr 2 <;> first | rfl | (apply congrArg ofFinset; ext z; simp only [mem_image]) | (ext z; simp only [mem_image])
    | iterate step =>
      have hh (x : HF A) := step.traced_transport e S T h p (Fin.cons x env)
      simp only [lift_cons] at hh
      have hx := tracedLoop_transport e p
        (fun x => step.traced S p (Fin.cons x env))
        (fun x => step.traced T p (Fin.cons x (fun j => lift e (env j)))) hh (p+1) emptyHF
      simpa only [Term.traced,lift_emptyHF] using hx
  theorem Formula.traced_transport (e : A ≃ B) (S : Input A) (T : Input B)
      (h : ∀ r a b, T.rel r (e a) (e b) = S.rel r a b) (p : ℕ)
      {n : ℕ} (f : Formula n) (env : Fin n → HF A) :
      f.traced T p (fun j => lift e (env j)) =
        ((f.traced S p env).1,(f.traced S p env).2.image (lift e)) := by
    cases f with
    | equal a b =>
      simp only [Formula.traced,a.traced_transport e S T h p env,b.traced_transport e S T h p env,
        Equiv.apply_eq_iff_eq,image_union]
    | input r a b =>
      simp only [Formula.traced,a.traced_transport e S T h p env,b.traced_transport e S T h p env,
        lift_inputHF e S T h,image_union]
    | neg a => simp only [Formula.traced,a.traced_transport e S T h p env]
    | and a b | or a b =>
      simp only [Formula.traced,a.traced_transport e S T h p env,b.traced_transport e S T h p env,image_union]
    | wsc step choice witness output => simp only [Formula.traced,image_empty]
end

end

end WitnessedChoice.BGS

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation

lemma realPolynomial_majorant (p : Polynomial ℝ) :
    ∃ q : Polynomial ℕ, ∀ n : ℕ, p.eval (n : ℝ) ≤ ((q.eval n : ℕ) : ℝ) := by
  induction p using Polynomial.induction_on' with
  | add a b ha hb =>
    obtain ⟨q,hq⟩ := ha
    obtain ⟨r,hr⟩ := hb
    refine ⟨q+r,fun n => ?_⟩
    simpa only [Polynomial.eval_add,Nat.cast_add] using add_le_add (hq n) (hr n)
  | monomial k a =>
    refine ⟨Polynomial.monomial k ⌈|a|⌉₊,fun n => ?_⟩
    simp only [Polynomial.eval_monomial,Nat.cast_mul,Nat.cast_pow]
    apply mul_le_mul_of_nonneg_right ((le_abs_self a).trans (Nat.le_ceil _))
    positivity

lemma resource_majorant (p : Polynomial ℝ) :
    ∃ q : Polynomial ℕ, ∀ n : ℕ, resource p n ≤ q.eval n := by
  obtain ⟨q,hq⟩ := realPolynomial_majorant p
  refine ⟨q,fun n => ?_⟩
  have hh := Nat.floor_mono (hq n)
  simpa only [resource,Nat.floor_natCast] using hh

end

end WitnessedChoice.BGS

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary WitnessedSeparation.HFCoding

open WitnessedSeparation.Grid WitnessedSeparation.Counting Finset

open WitnessedSeparation.Operational (lift)

variable {n : ℕ}

lemma Formula.grid_trace_invariant (f : Formula 0) (b : Vertex n → Grid.Scalar)
    (p : ℕ) : ∀ g : BoxGroup n, ∀ x ∈ (f.traced (atomInput b) p Fin.elim0).2,
      g • x ∈ (f.traced (atomInput b) p Fin.elim0).2 := by
  intro g x hx
  have ht := f.traced_transport (actionIso (b := b) g).toEquiv (atomInput b) (atomInput b)
    (fun r a c => (actionIso g).rel_eq r a c) p Fin.elim0
  have he : (fun j : Fin 0 => lift (actionIso (b := b) g).toEquiv (Fin.elim0 j)) = Fin.elim0 :=
    funext (fun j => Fin.elim0 j)
  rw [he] at ht
  have hm : g • x ∈ (f.traced (atomInput b) p Fin.elim0).2.image
      (lift (actionIso (b := b) g).toEquiv) := mem_image.mpr ⟨x,hx,rfl⟩
  exact (congrArg (fun z => g • x ∈ z.2) ht).mpr hm

lemma Formula.grid_trace_supported (f : Formula 0) (b : Vertex n → Grid.Scalar)
    (hn : 1 ≤ n) (p K N q : ℕ) (hN : 0 < N)
    (hb : (f.traced (atomInput b) p Fin.elim0).2.card ≤ K) (hK : K ≤ N^q) :
    ∀ x ∈ (f.traced (atomInput b) p Fin.elim0).2,
      HereditarilySupported (G := CentralGroup n)
        ⌈2*(n+1:ℝ)*((q:ℝ)*Real.logb 3 N)^2⌉₊ x := by
  apply invariant_family_hereditarily_supported hn _ (f.grid_trace_invariant b p)
    (fun x hx y hy => f.traced_closed (atomInput b) p Fin.elim0 x hx
      (closure_member_subset hy (mem_closure_self y))) N hN (q:ℝ) (by positivity)
  rw [Real.rpow_natCast]
  exact_mod_cast hb.trans hK

lemma Formula.grid_traced_agrees (f : Formula 0) (hf : f.wscCount = 0)
    {m M N : ℕ} (vstar : Vertex n) (hn : 1 ≤ n) (p K q : ℕ)
    (hN : 0 < N) (hK : K ≤ N^q)
    (hb : ∀ i : Bool, (f.traced (atomInput (twoCharges vstar i)) p Fin.elim0).2.card ≤ K)
    (hm : f.graphWidth ≤ m) (hmpos : 0 < m)
    (hs : 0 < ⌈2*(n+1:ℝ)*((q:ℝ)*Real.logb 3 N)^2⌉₊)
    (hwidth : max 4 (m+1)*⌈2*(n+1:ℝ)*((q:ℝ)*Real.logb 3 N)^2⌉₊ ≤ M)
    (hhom : (7*(max 2 m*⌈2*(n+1:ℝ)*((q:ℝ)*Real.logb 3 N)^2⌉₊):ℝ)+
      7*((6*(max 2 m*⌈2*(n+1:ℝ)*((q:ℝ)*Real.logb 3 N)^2⌉₊):ℝ)/boxConstant)^((3:ℝ)/2)+1 ≤ M)
    (hgiant : GiantBound n M) :
    (f.traced (atomInput (twoCharges vstar false)) p Fin.elim0).1 =
      (f.traced (atomInput (twoCharges vstar true)) p Fin.elim0).1 := by
  let s := ⌈2*(n+1:ℝ)*((q:ℝ)*Real.logb 3 N)^2⌉₊
  let D := programDomain (twoCharges vstar) (s := s)
  let C := programHF (twoCharges vstar) (s := s)
  have ht (i : Bool) : AdmissibleTrace (D i) K
      (f.traced (atomInput (twoCharges vstar i)) p Fin.elim0).2 := by
    intro x hx
    refine ⟨f.grid_trace_supported (twoCharges vstar i) hn p K N q hN (hb i) hK x hx,?_⟩
    exact (card_le_card ((elements_subset_closure x).trans
      (f.traced_closed (atomInput (twoCharges vstar i)) p Fin.elim0 x hx))).trans (hb i)
  have hu := f.uniform_graph D C (program_domain_transitive (twoCharges vstar))
    (program_pure (twoCharges vstar) hn) (program_atom_mem (twoCharges vstar) hs)
    (program_mem_uniform (twoCharges vstar)) (program_set_uniform (twoCharges vstar))
    (fun i => atomInput (twoCharges vstar i)) (op_input_uniform (twoCharges vstar)) p K true hm
  have he : UniformDefinable C m 0 (fun i _ =>
      (f.traced (atomInput (twoCharges vstar i)) p Fin.elim0).1 = true) := by
    apply hu.congr
    intro i env
    have he : (fun j : Fin 0 => (env j).val) = Fin.elim0 := funext (fun j => Fin.elim0 j)
    constructor
    · intro hg
      have hh := f.graph_sound (D i) (atomInput (twoCharges vstar i)) p K
        (program_domain_transitive (twoCharges vstar) i) true env hg
      simpa only [he] using hh.symm
    · intro hg
      apply f.graph_complete (D i) (atomInput (twoCharges vstar i)) p K
        (program_domain_transitive (twoCharges vstar) i)
        (program_pure (twoCharges vstar) hn i 0) hf true env
      · simpa only [he] using ht i
      · simpa only [he] using hg.symm
  obtain ⟨φ,hφ,hφsem⟩ := he (Fin.elim0 : Fin 0 → Fin m)
  have hfree : φ.free = ∅ := subset_empty.mp (by simpa using hφ)
  let v : Fin m → Domain (D false) := fun _ => ⟨ordinal 0,program_pure (twoCharges vstar) hn false 0⟩
  let w : Fin m → Domain (D true) := fun _ => ⟨ordinal 0,program_pure (twoCharges vstar) hn true 0⟩
  let := atom_nonempty hn (0 : Vertex n → Grid.Scalar)
  let := atom_nonempty hn (Pi.single vstar 1)
  apply Bool.eq_iff_iff.mpr
  exact (hφsem false v).symm.trans ((grid_hf_transfer hn hs hmpos vstar
    hwidth hhom hgiant φ hfree v w).trans (hφsem true w))

end

end WitnessedChoice.BGS

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

open WitnessedSeparation.Grid WitnessedSeparation.Quantitative

theorem Sentence.agrees_on_some_grid_pair (ψ : Sentence) (hψ : ψ.isCPT) :
    ∃ n : ℕ, 1 ≤ n ∧ ∀ vstar : Vertex n,
      ψ.eval (gridInput (0 : Vertex n → Grid.Scalar)) =
        ψ.eval (gridInput (Pi.single vstar 1)) := by
  obtain ⟨r,hr⟩ := resource_majorant ψ.polynomial
  let Q : Polynomial ℕ := ψ.formula.traceBound.comp (Polynomial.X+r+1)
  obtain ⟨c,d,hcd⟩ := PolynomialCost.eval_bound Q
  let q := timeExponent c d
  let m := ψ.formula.graphWidth+1
  obtain ⟨n,hn,hnum⟩ := exists_numeric_box q (by
    have h := timeExponent_ge_two c d; omega) m
  refine ⟨n,hn,fun vstar => ?_⟩
  let N := atomSizeConstant*(n+1)^3
  let p := resource ψ.polynomial (Fintype.card (Atom (0 : Vertex n → Grid.Scalar)))
  let K := N^q
  have hN : 2 ≤ N := hnum.1
  have hc : Fintype.card (Atom (0 : Vertex n → Grid.Scalar)) =
      Fintype.card (Atom (Pi.single vstar 1)) := atom_card_independent hn _ _
  have hinput (i : Bool) : Fintype.card (Atom (twoCharges vstar i)) ≤ N :=
    (atom_card_bounds hn _).2
  have hres (i : Bool) : resource ψ.polynomial
      (Fintype.card (Atom (twoCharges vstar i))) = p := by
    cases i
    · rfl
    · exact congrArg (resource ψ.polynomial) hc.symm
  have hp : p ≤ r.eval N := (hr _).trans (PolynomialCost.eval_mono r (hinput false))
  have hb (i : Bool) : (ψ.formula.traced (atomInput (twoCharges vstar i)) p Fin.elim0).2.card ≤ K := by
    calc
      _ ≤ ψ.formula.traceBound.eval (N+r.eval N+1) :=
        ψ.formula.traced_card_le _ p Fin.elim0 _ (by
          simp only [tracePotential,Fin.sum_univ_zero,Nat.add_zero]
          have hi := hinput i
          omega)
      _ = Q.eval N := by simp only [Q,Polynomial.eval_comp,Polynomial.eval_add,
        Polynomial.eval_X,Polynomial.eval_one]
      _ ≤ c*(N+1)^d := hcd N
      _ ≤ K := (polynomial_bounds c d N hN).2.2.1
  have hh := ψ.formula.grid_traced_agrees hψ (m := m) vstar hn p K q
    (by omega : 0 < N) (le_refl K) hb (by omega) (by omega)
    hnum.2.1 hnum.2.2.1 (by simpa only [N,Nat.cast_mul] using hnum.2.2.2.1) hnum.2.2.2.2
  dsimp only [Sentence.eval,gridInput]
  rw [ψ.formula.eval_traced _ _ hψ,ψ.formula.eval_traced _ _ hψ]
  change some (ψ.formula.traced (atomInput (0 : Vertex n → Grid.Scalar)) p Fin.elim0).1 = _
  rw [← hc]
  exact congrArg some hh

end

end WitnessedChoice.BGS

end

end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_Syntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace WitnessedChoice

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

variable {A : Type}

theorem stateCode_fixed_of_pointwise {g : Equiv.Perm A} {x : Finset A}
    (h : ∀ a ∈ x, g a = a) : g • stateCode x = stateCode x := by
  rw [smul_stateCode, stateCode_inj]
  calc
    x.image g = x.image id := Finset.image_congr h
    _ = x := Finset.image_id

namespace Selection

variable {P : Selection A}

theorem advance_mono (x : Finset A) (c : Option A) : x ⊆ advance x c := by
  cases c
  · exact Finset.Subset.refl _
  · exact Finset.subset_insert _ _

theorem advance_card {x : Finset A} {c : Option A} (h : x ≠ advance x c) :
    (advance x c).card = x.card + 1 := by
  cases c with
  | none => exact (h rfl).elim
  | some a =>
    change (insert a x).card = _
    apply Finset.card_insert_of_notMem
    intro ha
    exact h (Finset.insert_eq_of_mem ha).symm

theorem Prefix.restrict {b c k l} (h : P.Prefix b c k) (hle : l ≤ k) :
    P.Prefix b c l :=
  ⟨h.1, fun i hi => h.2 i (Nat.lt_of_lt_of_le hi hle)⟩

theorem Prefix.monotone {b c k} (h : P.Prefix b c k) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ k) : b i ⊆ b j := by
  induction j, hij using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ j hij ih =>
    have hjk : j < k := by omega
    have hs := h.2 j hjk
    rw [hs.2]
    exact (ih (by omega)).trans (advance_mono _ _)

theorem Prefix.card_eq {b c k} (h : P.Prefix b c k)
    (hstrict : ∀ i < k, b i ≠ b (i+1)) : ∀ i ≤ k, (b i).card = i := by
  intro i hi
  induction i with
  | zero => simp [h.1]
  | succ i ih =>
    have hic : i < k := by omega
    have hs := h.2 i hic
    rw [hs.2, advance_card (by simpa [hs.2] using hstrict i hic), ih (by omega)]

theorem FirstStabilization.length_le [Fintype A] {b c t} (h : P.FirstStabilization b c t) :
    t ≤ Fintype.card A := by
  have hc := (h.1.restrict (Nat.le_succ t)).card_eq h.2.1 t le_rfl
  rw [← hc]
  exact Finset.card_le_univ _

theorem Filtered.history {S : Input A} {α : HF A} (hf : P.Filtered S α)
    {b c k} (hp : P.Prefix b c k) {i : ℕ} (hi : i ≤ k)
    {g : Equiv.Perm A} (hg : g ∈ P.witnesses (b i)) : HistoryAut S α b i g := by
  refine ⟨hf.2.1 _ _ hg, ?_⟩
  intro j hji
  apply stateCode_fixed_of_pointwise
  intro a ha
  exact hf.2.2 _ _ hg _ (hp.monotone hji hi ha)

theorem Filtered.witnessed {S : Input A} {α : HF A} (hf : P.Filtered S α)
    {b c k} (hp : P.Prefix b c k) {i : ℕ} (hi : i ≤ k) (terminal : Finset A) :
    P.WitnessedAt S α b terminal i := by
  refine ⟨choices_nonempty _, fun g hg => hf.history hp hi hg, ?_⟩
  intro u hu v hv
  by_cases ht : (P.candidates (b i)).Nonempty ∧ P.TransitiveAt (b i)
  · simp only [choices, ite_eq_left ht, Finset.mem_image] at hu hv
    obtain ⟨a, ha, rfl⟩ := hu
    obtain ⟨a', ha', rfl⟩ := hv
    obtain ⟨g, hg, hga⟩ := ht.2 a ha a' ha'
    refine ⟨g, hg, ?_⟩
    simpa [choiceCode] using congrArg atom hga
  · have hu' : u = none := by simpa [choices, ht] using hu
    have hv' : v = none := by simpa [choices, ht] using hv
    subst u; subst v
    exact ⟨1, hf.1 _, one_smul _ _⟩

end Selection

end

end WitnessedChoice

end

section

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

variable {A : Type} [Fintype A]

namespace Realizes

variable {P : Selection A} {step : HF A → HF A → Result (HF A)}
  {choice : HF A → Result (HF A)} {witness : HF A → HF A → Result (HF A)}
  (hr : Realizes P step choice witness)

include hr

theorem prefix_decode {b c : ℕ → HF A} {k : ℕ} (hp : ChoicePrefix step choice b c k) :
    P.Prefix (decodeState ∘ b) (decodeChoice ∘ c) k ∧
    (∀ i ≤ k, b i = stateCode (decodeState (b i))) ∧
    (∀ i < k, c i = choiceCode (decodeChoice (c i))) := by
  have h0 : decodeState (b 0) = ∅ := by simp [hp.1, emptyHF, decodeState]
  have hstates : ∀ i ≤ k, b i = stateCode (decodeState (b i)) := by
    intro i hi
    induction i with
    | zero => simp [hp.1, emptyHF, stateCode, decodeState]
    | succ i ih =>
      have hik : i < k := by omega
      obtain ⟨⟨D, hD, hc⟩, hs⟩ := hp.2 i hik
      have hb := ih (by omega)
      rw [hb, hr.choice_eq] at hD
      cases hD
      simp only [elements_ofFinset] at hc
      obtain ⟨a, ha, hac⟩ := Finset.mem_image.mp hc
      have he := hr.step_eq (decodeState (b i)) a ha
      rw [← hb, hac] at he
      rw [he] at hs
      have hs' := Option.some.inj hs
      rw [← hs', decodeState_code]
  have hchoices : ∀ i < k, ∃ a ∈ P.choices (decodeState (b i)), choiceCode a = c i := by
    intro i hi
    obtain ⟨⟨D, hD, hc⟩, _⟩ := hp.2 i hi
    rw [hstates i (by omega), hr.choice_eq] at hD
    cases hD
    simp only [elements_ofFinset] at hc
    exact Finset.mem_image.mp hc
  refine ⟨⟨h0, ?_⟩, hstates, ?_⟩
  · intro i hi
    obtain ⟨a, ha, hac⟩ := hchoices i hi
    have hd : decodeChoice (c i) = a := by rw [← hac, decodeChoice_code]
    refine ⟨by simpa only [Function.comp_apply, hd] using ha, ?_⟩
    obtain ⟨_, hs⟩ := hp.2 i hi
    rw [hstates i (by omega), ← hac, hr.step_eq _ _ ha] at hs
    have he := Option.some.inj hs
    simp only [Function.comp_apply, hd]
    rw [← he, decodeState_code]
  · intro i hi
    obtain ⟨a, _, hac⟩ := hchoices i hi
    rw [← hac, decodeChoice_code]

theorem first_decode {b c : ℕ → HF A} {t : ℕ} (hp : FirstPath step choice b c t) :
    P.FirstStabilization (decodeState ∘ b) (decodeChoice ∘ c) t := by
  obtain ⟨hpre, hb, _⟩ := hr.prefix_decode hp.1
  refine ⟨hpre, ?_, congrArg decodeState hp.2.2⟩
  intro i hi he
  apply hp.2.1 i hi
  rw [hb i (by omega), hb (i+1) (by omega)]
  exact congrArg stateCode he

theorem good {S : Input A} {α : HF A} (hf : P.Filtered S α)
    (p : ℕ) (hp : Fintype.card A + 2 ≤ p) (free : Finset (Fin 1))
    (output : HF A → Result Bool) (hout : ∀ x : Finset A, (output (stateCode x)).isSome) :
    GoodWSC S p free (Fin.cons α Fin.elim0) step choice witness output := by
  constructor
  · intro b c k hk hstrict
    obtain ⟨hpre, hb, hc⟩ := hr.prefix_decode hk
    have hs : ∀ i < k, (decodeState ∘ b) i ≠ (decodeState ∘ b) (i+1) := by
      intro i hi he
      apply hstrict i hi
      rw [hb i (by omega), hb (i+1) (by omega)]
      exact congrArg stateCode he
    have hn : k ≤ Fintype.card A := by
      rw [← hpre.card_eq hs k le_rfl]
      exact Finset.card_le_univ _
    refine ⟨by omega, ?_, ofFinset ((P.choices (decodeState (b k))).image choiceCode), ?_, ?_, ?_⟩
    · rw [hb k le_rfl, TC_stateCode, Finset.card_image_of_injective _ atom_injective]
      exact (Finset.card_le_univ _).trans (by omega)
    · rw [hb k le_rfl, hr.choice_eq, decodeState_code]
    · simpa only [elements_ofFinset, Finset.image_nonempty] using P.choices_nonempty (decodeState (b k))
    · intro u hu
      simp only [elements_ofFinset] at hu
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
      rw [hb k le_rfl, hr.step_eq _ _ ha]
      simp
  · intro b c t ht
    obtain ⟨hpre, hb, hc⟩ := hr.prefix_decode ht.1
    have hfirst := hr.first_decode ht
    have hn := hfirst.length_le
    refine ⟨by omega, ?_, ?_⟩
    · intro i hi
      let x := decodeState (b i)
      let z := decodeState (b t)
      refine ⟨ofFinset ((P.choices x).image choiceCode),
        ofFinset ((P.witnesses x).image permutationGraph), ?_, ?_, ?_⟩
      · rw [hb i (by omega), hr.choice_eq]
      · rw [hb t (by omega), hb i (by omega), hr.witness_eq]
      · obtain ⟨_, hwnd, htrans⟩ := hf.witnessed hpre (by omega : i ≤ t+1) z
        refine ⟨by simp, ?_, ?_⟩
        · intro w hw
          simp only [elements_ofFinset] at hw
          obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hw
          obtain ⟨hpar, hhist⟩ := hwnd g hg
          refine ⟨g, rfl, hpar.1, ?_, ?_⟩
          · intro j hj
            have hj0 : j = 0 := Fin.eq_zero j
            subst j
            exact hpar.2
          · intro j hj
            rw [hb j (by omega)]
            exact hhist j hj
        · intro u hu v hv
          simp only [elements_ofFinset] at hu
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
          simp only [elements_ofFinset] at hv
          obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp hv
          obtain ⟨g, hg, he⟩ := htrans a ha a' ha'
          refine ⟨g, ?_, he⟩
          simp only [elements_ofFinset]
          apply Finset.mem_image.mpr
          exact ⟨g, hg, rfl⟩
    · rw [hb t (by omega)]
      exact hout _

theorem boolean {S : Input A} {α : HF A} (hf : P.Filtered S α)
    (p : ℕ) (hp : Fintype.card A + 2 ≤ p) (free : Finset (Fin 1))
    (output : HF A → Result Bool) (hout : ∀ x : Finset A, (output (stateCode x)).isSome) :
    ∃ b, witnessedIteration S p free (Fin.cons α Fin.elim0) step choice witness output = some b := by
  unfold witnessedIteration
  rw [ite_eq_left (hr.good hf p hp free output hout)]
  exact ⟨_, rfl⟩

end Realizes

end

end WitnessedChoice.BGS

end

section

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

variable {A : Type} [Fintype A]

lemma Term.eval_letIn (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (v : Term n) (b : Term (n+1)) (env : Fin n → HF A) {x y : HF A}
    (hv : v.eval S p env = some x) (hb : b.eval S p (Fin.cons x env) = some y) :
    (v.letIn b).eval S p env = some y := by
  simp only [Term.letIn,eval,eval_singleton S p v env hv,Option.bind_some]
  have he : collect (Hereditary.singleton x) (fun z => Formula.truth.eval S p (Fin.cons z env))
      (fun z => b.eval S p (Fin.cons z env)) = some (Hereditary.singleton y) := by
    simp [collect,Formula.eval_truth,Hereditary.singleton,hb]
  rw [he,Option.map_some,uniqueHF_singleton]

end

end WitnessedChoice.BGS

end

end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_QuotedSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace WitnessedChoice

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

open RelationPools

variable {A : Type} [Fintype A]

omit [Fintype A] in
lemma smul_pair (g : Equiv.Perm A) (x y : HF A) :
    g • pair x y = pair (g • x) (g • y) := map_pair g x y

omit [Fintype A] in
lemma tupleCode_fixed (g : Equiv.Perm A) (xs : List (HF A))
    (h : ∀ x ∈ xs, g • x = x) : g • tupleCode xs = tupleCode xs := by
  induction xs with
  | nil => simp [tupleCode,ordinal,smul_ofFinset]
  | cons x xs ih =>
    simp only [tupleCode,smul_pair]
    rw [h x (by simp),ih (fun y hy => h y (by simp [hy]))]

omit [Fintype A] in
lemma parameterCode_fixed (g : Equiv.Perm A) (α : Fin 4 → Finset A)
    (h : ∀ i, (α i).image g = α i) : g • parameterCode α = parameterCode α := by
  apply tupleCode_fixed
  intro x hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  dsimp [Function.comp_apply]
  rw [smul_stateCode,h i]

variable (B : ℕ)

lemma one_mem_witnessPool (S : Input A) (valid : Prop)
    (C : Finset A → Finset (Relation A)) (x : Finset A) :
    (1 : Equiv.Perm A) ∈ witnessPool B S valid C x := by
  unfold witnessPool
  split_ifs <;> simp

lemma witnessPool_filter (S : Input A) (valid : Prop)
    (C : Finset A → Finset (Relation A)) (x : Finset A) {g : Equiv.Perm A}
    (h : g ∈ witnessPool B S valid C x) : PoolFilter S x g := by
  unfold witnessPool at h
  split_ifs at h
  · rcases Finset.mem_insert.mp h with rfl | h
    · exact ⟨(fullAut S).one_mem,by simp,by simp⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
      exact h.1
  · have hg : g = 1 := Finset.mem_singleton.mp h
    subst g
    exact ⟨(fullAut S).one_mem,by simp,by simp⟩

theorem guardedSelection_filtered (S : Input A) (valid : Prop)
    (D : Finset A → Finset A) (C : Finset A → Finset (Relation A))
    (α : Fin 4 → Finset A) (hα : ∀ i, α i ∈ blocks S) :
    (guardedSelection B S valid D C).Filtered S (parameterCode α) := by
  refine ⟨one_mem_witnessPool B S valid C,?_,?_⟩
  · intro x g hg
    obtain ⟨ha,hb,_⟩ := witnessPool_filter B S valid C x hg
    exact ⟨ha,parameterCode_fixed g α (fun i => hb (α i) (hα i))⟩
  · intro x g hg
    exact (witnessPool_filter B S valid C x hg).2.2

end

end WitnessedChoice



namespace WitnessedChoice.BGS





noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary RelationPools

namespace QuotedTerm

variable {n : ℕ}

variable {A : Type} [Fintype A] (S : Input A) (env : Fin n → HF A)

lemma meaning_edgeRow (a : QuotedTerm n) (x : A) (ha : a.meaning S env = atom x) :
    (edgeRow a).meaning S env = stateCode (WitnessedChoice.edgeRow S x) := by
  simp only [edgeRow,meaning_filter,meaning_edgeAtoms,stateCode,elements_ofFinset,
    QuotedFormula.meaning_input,meaning_up,meaning_var,Fin.cons_zero,ha]
  apply ofFinset_inj.mpr
  ext z
  simp only [Finset.mem_filter,Finset.mem_image,WitnessedChoice.edgeRow]
  constructor
  · rintro ⟨⟨b,hb,rfl⟩,hr⟩
    exact ⟨b,⟨hb,by simpa only [inputHF_atoms] using hr⟩,rfl⟩
  · rintro ⟨b,⟨hb,hr⟩,rfl⟩
    exact ⟨⟨b,hb,rfl⟩,by simpa only [inputHF_atoms] using hr⟩

lemma meaning_vertexRow (a : QuotedTerm n) (x : A) (ha : a.meaning S env = atom x) :
    (vertexRow a).meaning S env = stateCode (WitnessedChoice.vertexRow S x) := by
  simp only [vertexRow,meaning_filter,meaning_configAtoms,stateCode,elements_ofFinset,
    QuotedFormula.meaning_input,meaning_up,meaning_var,Fin.cons_zero,ha]
  apply ofFinset_inj.mpr
  ext z
  simp only [Finset.mem_filter,Finset.mem_image,WitnessedChoice.vertexRow]
  constructor
  · rintro ⟨⟨b,hb,rfl⟩,hr⟩
    exact ⟨b,⟨hb,by simpa only [inputHF_atoms] using hr⟩,rfl⟩
  · rintro ⟨b,⟨hb,hr⟩,rfl⟩
    exact ⟨⟨b,hb,rfl⟩,by simpa only [inputHF_atoms] using hr⟩

@[simp] lemma meaning_edgeBlocks : (edgeBlocks : QuotedTerm n).meaning S env =
    ofFinset ((WitnessedChoice.edgeBlocks S).image stateCode) := by
  simp only [edgeBlocks,meaning_map,meaning_edgeAtoms,stateCode,elements_ofFinset,
    Finset.image_image,WitnessedChoice.edgeBlocks,Function.comp_def]
  congr 2
  funext x
  exact meaning_edgeRow S (Fin.cons (atom x) env) (.var 0) x rfl

@[simp] lemma meaning_vertexBlocks : (vertexBlocks : QuotedTerm n).meaning S env =
    ofFinset ((WitnessedChoice.vertexBlocks S).image stateCode) := by
  simp only [vertexBlocks,meaning_map,meaning_configAtoms,stateCode,elements_ofFinset,
    Finset.image_image,WitnessedChoice.vertexBlocks,Function.comp_def]
  congr 2
  funext x
  exact meaning_vertexRow S (Fin.cons (atom x) env) (.var 0) x rfl

@[simp] lemma meaning_blocks : (blocks : QuotedTerm n).meaning S env =
    ofFinset ((WitnessedChoice.blocks S).image stateCode) := by
  simp only [blocks,meaning_cup,meaning_edgeBlocks,meaning_vertexBlocks,elements_ofFinset,WitnessedChoice.blocks]
  apply ofFinset_inj.mpr
  ext z
  simp only [Finset.mem_union,Finset.mem_image]
  aesop

lemma meaning_composition (l c : QuotedTerm n) (r t : Relation A)
    (hl : l.meaning S env = relationCode r) (hc : c.meaning S env = relationCode t) :
    (composition l c).meaning S env = relationCode (compose r t) := by
  simp only [composition,meaning_relation,QuotedFormula.meaning_existsIn,meaning_atoms,
    exists_stateCode,Finset.mem_univ,true_and,QuotedFormula.meaning_and,
    QuotedFormula.meaning_link,meaning_var,Fin.cons_zero,Fin.cons_one,
    fin_cons_two,meaning_up,hl,hc,pair_mem_relationCode]
  rfl

end QuotedTerm

end





noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary RelationPools

variable {A : Type} [Fintype A]

lemma functionalOnto_iff (r : Relation A) : FunctionalOnto r ↔ ∃ g : Equiv.Perm A, r = graph g := by
  constructor
  · intro h
    let f : A → A := fun a => (h.1 a).choose
    have hf (a : A) : (a,f a) ∈ r ∧ ∀ b, (a,b) ∈ r → b = f a := (h.1 a).choose_spec
    have hs : Function.Surjective f := by
      intro b
      obtain ⟨a,hab⟩ := h.2 b
      exact ⟨a,((hf a).2 b hab).symm⟩
    let g : Equiv.Perm A := Equiv.ofBijective f ⟨Finite.injective_iff_surjective.mpr hs,hs⟩
    refine ⟨g,?_⟩
    ext ⟨a,b⟩
    simp only [mem_graph]
    constructor
    · intro hab
      exact ((hf a).2 b hab).symm
    · intro he
      rw [←he]
      exact (hf a).1
  · rintro ⟨g,rfl⟩
    constructor
    · intro a
      exact ⟨g a,by simp,fun b hb => (mem_graph g a b).mp hb |>.symm⟩
    · intro b
      exact ⟨g.symm b,by simp⟩

lemma rawFilter_graph (S : Input A) (x : Finset A) (g : Equiv.Perm A) :
    RawFilter S x (graph g) ↔ PoolFilter S x g := by
  constructor
  · rintro ⟨_,hR,hB,hx⟩
    refine ⟨?_,?_,?_⟩
    · intro R a b
      exact (hR R a b (g a) (g b) (by simp) (by simp)).symm
    · intro u hu
      apply Finset.eq_of_subset_of_card_le
      · intro y hy
        obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hy
        exact hB u hu a ha (g a) (by simp)
      · rw [Finset.card_image_of_injective _ g.injective]
    · intro a ha
      exact (mem_graph g a a).mp (hx a ha)
  · rintro ⟨hR,hB,hx⟩
    refine ⟨(functionalOnto_iff _).mpr ⟨g,rfl⟩,?_,?_,?_⟩
    · intro R a a' b b' hab ha'b'
      rw [←(mem_graph g a b).mp hab,←(mem_graph g a' b').mp ha'b']
      exact (hR R a a').symm
    · intro u hu a ha b hab
      rw [←(mem_graph g a b).mp hab,←hB u hu]
      exact Finset.mem_image.mpr ⟨a,ha,rfl⟩
    · intro a ha
      exact (mem_graph g a a).mpr (hx a ha)

lemma rawFilter_iff (S : Input A) (x : Finset A) (r : Relation A) :
    RawFilter S x r ↔ ∃ g : Equiv.Perm A, r = graph g ∧ PoolFilter S x g := by
  constructor
  · intro h
    obtain ⟨g,rfl⟩ := (functionalOnto_iff r).mp h.1
    exact ⟨g,rfl,(rawFilter_graph S x g).mp h⟩
  · rintro ⟨g,rfl,hg⟩
    exact (rawFilter_graph S x g).mpr hg

namespace QuotedFormula

variable {n : ℕ}

variable (S : Input A) (env : Fin n → HF A)

lemma meaning_functional (r : QuotedTerm n) (R : Relation A) (hr : r.meaning S env = relationCode R) :
    (functional r).meaning S env ↔ ∀ a, ∃! b, (a,b) ∈ R := by
  simp [functional,hr,ExistsUnique,atom_injective.eq_iff,pairCode]
  constructor
  · intro h a
    obtain ⟨b,hb,hu⟩ := h a
    exact ⟨b,hb,fun c hc => hu c a c hc rfl rfl⟩
  · intro h a
    obtain ⟨b,hb,hu⟩ := h a
    refine ⟨b,hb,?_⟩
    rintro c d e hc rfl rfl
    exact hu e hc

lemma meaning_onto (r : QuotedTerm n) (R : Relation A) (hr : r.meaning S env = relationCode R) :
    (onto r).meaning S env ↔ ∀ b, ∃ a, (a,b) ∈ R := by
  simp [onto,hr,pairCode,atom_injective.eq_iff]

lemma meaning_preserves (r : QuotedTerm n) (R : Relation A) (hr : r.meaning S env = relationCode R) :
    (preserves r).meaning S env ↔ ∀ s a a' b b', (a,b) ∈ R → (a',b') ∈ R → S.rel s a a' = S.rel s b b' := by
  simp [preserves,hr,Bool.coe_iff_coe,and_imp,pairCode,atom_injective.eq_iff]
  aesop

lemma meaning_fixesBlocks (r : QuotedTerm n) (R : Relation A) (hr : r.meaning S env = relationCode R) :
    (fixesBlocks r).meaning S env ↔ ∀ u ∈ blocks S, ∀ a ∈ u, ∀ b, (a,b) ∈ R → b ∈ u := by
  simp [fixesBlocks,hr,stateCode,atom_injective.eq_iff,pairCode]
  aesop

lemma meaning_fixesState (x r : QuotedTerm n) (X : Finset A) (R : Relation A)
    (hx : x.meaning S env = stateCode X) (hr : r.meaning S env = relationCode R) :
    (fixesState x r).meaning S env ↔ ∀ a ∈ X, (a,a) ∈ R := by
  simp [fixesState,hx,hr,stateCode,atom_injective.eq_iff,pairCode]

lemma meaning_filter (x r : QuotedTerm n) (X : Finset A) (R : Relation A)
    (hx : x.meaning S env = stateCode X) (hr : r.meaning S env = relationCode R) :
    (filter x r).meaning S env ↔ RawFilter S X R := by
  rw [filter,meaning_and,meaning_and,meaning_and,meaning_and,
    meaning_functional S env r R hr,meaning_onto S env r R hr,
    meaning_preserves S env r R hr,meaning_fixesBlocks S env r R hr,
    meaning_fixesState S env x r X R hx hr]
  simp only [RawFilter,FunctionalOnto,and_assoc]

end QuotedFormula

end

end WitnessedChoice.BGS

end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_GuardedProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section


namespace WitnessedChoice.BGS
open Classical WitnessedSeparation WitnessedSeparation.Hereditary


namespace QuotedTerm
open RelationPools

section

variable {n : ℕ}

variable {A : Type} [Fintype A] (S : Input A) (env : Fin n → HF A)

lemma meaning_witnessRelations (B : ℕ) (valid : QuotedFormula n) (x C : QuotedTerm n)
    (X : Finset A) (cycles : Finset (Relation A))
    (hx : x.meaning S env = stateCode X)
    (hC : C.meaning S env = ofFinset (cycles.image relationCode)) :
    (witnessRelations B valid x C).meaning S env =
      ofFinset ((witnessPool B S (valid.meaning S env) (fun _ => cycles) X).image permutationGraph) := by
  have hcomp (l c : Relation A) :
      (composition (var (1 : Fin (n+2))) (var 0)).meaning S
        (Fin.cons (relationCode c) (Fin.cons (relationCode l) env)) = relationCode (compose l c) :=
    meaning_composition S _ _ _ _ _ rfl rfl
  have hf (l c : Relation A) :
      (QuotedFormula.filter x.up.up (composition (var (1 : Fin (n+2))) (var 0))).meaning S
        (Fin.cons (relationCode c) (Fin.cons (relationCode l) env)) ↔ RawFilter S X (compose l c) :=
    QuotedFormula.meaning_filter S _ _ _ _ _ (by simpa using hx) (hcomp l c)
  simp only [witnessRelations,meaning_cond,witnessPool]
  split_ifs with hv
  · simp only [meaning_cup,meaning_singleton,identity,localRelations,meaning_bind,
      meaning_up,hC,elements_ofFinset,comprehend,Hereditary.singleton]
    apply ofFinset_inj.mpr
    ext z
    simp only [Finset.mem_union,Finset.mem_singleton,Finset.mem_biUnion,Finset.mem_image,
      Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert]
    constructor
    · rintro (hz | ⟨l,⟨r,hr,rfl⟩,c,⟨⟨t,ht,rfl⟩,hf'⟩,hz⟩)
      · exact ⟨1,Or.inl rfl,(hz.trans (relationCode_graph 1)).symm⟩
      · have hh := (hf r t).mp hf'
        obtain ⟨g,hg,hfg⟩ := (rawFilter_iff S X _).mp hh
        refine ⟨g,Or.inr ⟨hfg,r,hr,t,ht,hg⟩,?_⟩
        rw [hcomp r t,hg,relationCode_graph] at hz
        exact hz
    · rintro ⟨g,(rfl | ⟨hfg,r,hr,t,ht,hg⟩),rfl⟩
      · exact Or.inl (relationCode_graph 1).symm
      · refine Or.inr ⟨relationCode r,⟨r,hr,rfl⟩,relationCode t,⟨⟨t,ht,rfl⟩,?_⟩,?_⟩
        · exact (hf r t).mpr ((rawFilter_iff S X _).mpr ⟨g,hg,hfg⟩)
        · rw [hcomp r t,hg,relationCode_graph]
  · simp only [meaning_singleton,identity,relationCode_graph,Finset.image_singleton,Hereditary.singleton]

lemma meaning_guardedChoice (D M : QuotedTerm n) (P : Selection A) (X : Finset A)
    (hD : D.meaning S env = stateCode (P.candidates X))
    (hM : M.meaning S env = ofFinset ((P.witnesses X).image permutationGraph)) :
    (guardedChoice D M).meaning S env = ofFinset ((P.choices X).image choiceCode) := by
  have hne : stateCode (P.candidates X) ≠ emptyHF ↔ (P.candidates X).Nonempty := by
    change stateCode (P.candidates X) ≠ stateCode ∅ ↔ _
    simp only [ne_eq,stateCode_inj,Finset.nonempty_iff_ne_empty]
  have hm (a b : A) :
      (∃ g ∈ (P.witnesses X), Hereditary.pair (atom a) (atom b) ∈ elements (permutationGraph g)) ↔
      ∃ g ∈ P.witnesses X, g a = b := by
    simp only [← relationCode_graph,pair_mem_relationCode,mem_graph]
  simp only [guardedChoice,meaning_cond,QuotedFormula.meaning_and,QuotedFormula.meaning_neg,
    QuotedFormula.meaning_eq,hD,meaning_empty,hne,QuotedFormula.meaning_allIn,
    all_stateCode,meaning_up,QuotedFormula.meaning_existsIn,hM,elements_ofFinset,
    QuotedFormula.meaning_link,meaning_var,Fin.cons_zero,Fin.cons_one,fin_cons_two,
    Finset.mem_image,exists_exists_and_eq_and,hm]
  unfold Selection.choices Selection.TransitiveAt
  split_ifs
  · simp only [stateCode,Finset.image_image,Function.comp_def,choiceCode]
  · simp only [meaning_singleton,meaning_empty,Finset.image_singleton,choiceCode,ordinal]
    rfl

end

variable {n : ℕ} {A : Type} [Fintype A] (S : Input A) (env : Fin n → HF A)

lemma meaning_selectionStep (x y : QuotedTerm n) (X : Finset A) (c : Option A)
    (hx : x.meaning S env = stateCode X) (hy : y.meaning S env = choiceCode c)
    (hc : ∀ a, c = some a → a ∈ WitnessedChoice.edgeAtoms S) :
    (selectionStep x y).meaning S env = stateCode (Selection.advance X c) := by
  have hne (a : A) : (emptyHF : HF A) ≠ atom a := by
    intro h
    have hh := congrArg isSet h
    simp [emptyHF] at hh
  simp only [selectionStep,meaning_cup,hx,meaning_inter,meaning_double,meaning_unique,hy,
    meaning_edgeAtoms,elements_ofFinset]
  cases c with
  | none =>
    simp only [choiceCode,show ordinal (A := A) 0 = emptyHF from rfl,uniqueHF_empty,Hereditary.double,elements_ofFinset,
      stateCode,Selection.advance]
    apply ofFinset_inj.mpr
    ext z
    simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton,
      Finset.mem_image]
    constructor
    · rintro (h | ⟨(rfl|rfl),a,ha,he⟩)
      · exact h
      all_goals exact (hne a he.symm).elim
    · exact Or.inl
  | some a =>
    have ha := hc a rfl
    simp only [choiceCode,uniqueHF_atom,Hereditary.double,elements_ofFinset,stateCode,
      Selection.advance,Finset.image_insert]
    apply ofFinset_inj.mpr
    ext z
    simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton,
      Finset.mem_image]
    constructor
    · rintro (h | ⟨(rfl|rfl),b,hb,he⟩)
      · exact Or.inr h
      · exact Or.inl rfl
      · exact (hne b he.symm).elim
    · rintro (rfl|h)
      · exact Or.inr ⟨Or.inl rfl,a,ha,rfl⟩
      · exact Or.inl h

end QuotedTerm


namespace CPTTerm

variable {n m : ℕ} {A : Type} [Fintype A]

lemma eval_value (t : CPTTerm n) (S : Input A) (p : Polynomial ℝ) (env : Fin n → HF A) :
    t.code.eval S p env = some (t.value S p env) := (t.code.total S p t.count env).choose_spec

lemma value_eq (t : CPTTerm n) (S : Input A) (p : Polynomial ℝ) (env : Fin n → HF A) {x : HF A}
    (h : t.code.eval S p env = some x) : t.value S p env = x :=
  Option.some.inj ((t.eval_value S p env).symm.trans h)

@[simp] lemma value_quoted (t : QuotedTerm n) (S : Input A) (p : Polynomial ℝ) (env : Fin n → HF A) :
    (quoted t).value S p env = t.meaning S env := (quoted t).value_eq S p env (t.correct S p env)

@[simp] lemma value_rename (t : CPTTerm n) (f : Fin n → Fin m) (S : Input A)
    (p : Polynomial ℝ) (env : Fin m → HF A) :
    (t.rename f).value S p env = t.value S p (env ∘ f) := by
  apply value_eq
  exact (t.code.eval_rename S p t.count f env).trans (t.eval_value S p _)

@[simp] lemma value_up (t : CPTTerm n) (S : Input A) (p : Polynomial ℝ) (env : Fin n → HF A) (x) :
    t.up.value S p (Fin.cons x env) = t.value S p env := value_rename _ _ _ _ _

@[simp] lemma value_letIn (t : CPTTerm n) (b : CPTTerm (n+1)) (S : Input A)
    (p : Polynomial ℝ) (env : Fin n → HF A) :
    (t.letIn b).value S p env = b.value S p (Fin.cons (t.value S p env) env) := by
  apply value_eq
  exact Term.eval_letIn S p t.code b.code env (t.eval_value S p env) (b.eval_value S p _)

end CPTTerm

namespace CPTFormula

variable {n m : ℕ} {A : Type} [Fintype A]

lemma eval_value (t : CPTFormula n) (S : Input A) (p : Polynomial ℝ) (env : Fin n → HF A) :
    t.code.eval S p env = some (t.value S p env) := (t.code.total S p t.count env).choose_spec

end CPTFormula


namespace QuotedTerm

variable {n : ℕ}

variable {A : Type} [Fintype A]

lemma mem_tupleProduct (k : ℕ) (r : QuotedTerm n) (S : Input A) (env : Fin n → HF A) (z : HF A) :
    z ∈ elements ((tupleProduct k r).meaning S env) ↔
      ∃ f : Fin k → HF A, (∀ i, f i ∈ elements (r.meaning S env)) ∧ tupleCode (List.ofFn f) = z := by
  induction k generalizing n z with
  | zero =>
    simp only [tupleProduct,meaning_singleton,meaning_empty,Hereditary.singleton,elements_ofFinset,
      Finset.mem_singleton,List.ofFn_zero,tupleCode]
    constructor
    · intro h; exact ⟨Fin.elim0,fun i => Fin.elim0 i,h.symm⟩
    · rintro ⟨f,hf,he⟩; exact he.symm
  | succ k ih =>
    simp only [tupleProduct,meaning_bind,meaning_map,meaning_pair,meaning_var,Fin.cons_zero,
      Fin.cons_one,elements_ofFinset,Finset.mem_biUnion,Finset.mem_image,ih,meaning_up]
    constructor
    · rintro ⟨a,ha,b,⟨f,hf,hb⟩,he⟩
      refine ⟨Fin.cons a f,?_,?_⟩
      · intro i; refine Fin.cases ha hf i
      · simp only [List.ofFn_succ,Fin.cons_zero,Fin.cons_succ,tupleCode]
        rw [hb,he]
    · rintro ⟨f,hf,he⟩
      refine ⟨f 0,hf 0,tupleCode (List.ofFn (fun i => f i.succ)),?_,?_⟩
      · exact ⟨fun i => f i.succ,fun i => hf i.succ,rfl⟩
      · simpa only [List.ofFn_succ,tupleCode] using he

lemma mem_blockParameters (S : Input A) (env : Fin n → HF A) (z : HF A) :
    z ∈ elements ((blockParameters : QuotedTerm n).meaning S env) ↔
      ∃ α : Fin 4 → Finset A, (∀ i, α i ∈ WitnessedChoice.vertexBlocks S) ∧ parameterCode α = z := by
  rw [blockParameters,mem_tupleProduct]
  simp only [meaning_vertexBlocks,elements_ofFinset]
  constructor
  · rintro ⟨f,hf,hz⟩
    have h (i) := Finset.mem_image.mp (hf i)
    choose α hα hαf using h
    refine ⟨α,hα,?_⟩
    have he : stateCode ∘ α = f := funext hαf
    simpa only [parameterCode,he] using hz
  · rintro ⟨α,hα,hz⟩
    refine ⟨stateCode ∘ α,?_,hz⟩
    intro i
    exact Finset.mem_image.mpr ⟨α i,hα i,rfl⟩

end QuotedTerm

lemma collect_on {A : Type} (r : HF A) (guard : HF A → Result Bool) (body : HF A → Result (HF A))
    (g : HF A → Bool) (b : HF A → HF A)
    (hg : ∀ x ∈ elements r, guard x = some (g x))
    (hb : ∀ x ∈ elements r, g x = true → body x = some (b x)) :
    collect r guard body = some (ofFinset (((elements r).filter (fun x => g x = true)).image b)) := by
  have hgood : (∀ x ∈ elements r, (guard x).isSome) ∧
      (∀ x ∈ elements r, guard x = some true → (body x).isSome) := by
    constructor
    · intro x hx; rw [hg x hx]; simp
    · intro x hx ht
      rw [hg x hx] at ht
      rw [hb x hx (Option.some.inj ht)]
      simp
  rw [collect,ite_eq_left hgood]
  apply congrArg some
  apply ofFinset_inj.mpr
  have hf : (elements r).filter (fun x => guard x = some true) =
      (elements r).filter (fun x => g x = true) := Finset.filter_congr (by
        intro x hx
        rw [hg x hx,Option.some.injEq])
  rw [hf]
  apply Finset.image_congr
  intro x hx
  obtain ⟨hx,ht⟩ := Finset.mem_filter.mp hx
  change (body x).getD emptyHF = b x
  rw [hb x hx ht,Option.getD_some]

lemma Formula.eval_existsIn_on {A : Type} [Fintype A] (S : Input A) (p : Polynomial ℝ) {n : ℕ}
    (r : Term n) (a : Formula (n+1)) (env : Fin n → HF A)
    {rv : HF A} {av : HF A → Bool} (hr : r.eval S p env = some rv)
    (ha : ∀ x ∈ elements rv, a.eval S p (Fin.cons x env) = some (av x)) :
    (Formula.existsIn r a).eval S p env = some (decide (∃ x ∈ elements rv, av x = true)) := by
  simp only [Formula.existsIn,Formula.eval,Term.eval,hr,Option.bind_some]
  rw [collect_on rv _ _ av (fun _ => emptyHF) ha (by intros; rfl)]
  simp only [lift₂,Option.bind_some,Option.map_some,Option.some.injEq]
  have he : ofFinset (((elements rv).filter (fun x => av x = true)).image (fun _ => (emptyHF : HF A))) = emptyHF ↔
      ¬ ∃ x ∈ elements rv, av x = true := by
    rw [emptyHF,ofFinset_inj,Finset.image_eq_empty]
    simp
  simp only [he,decide_not,Bool.not_not]


section

open RelationPools

variable {A : Type} [Fintype A]

namespace CPTTerm

variable {n : ℕ}

@[simp] lemma value_normalizeCandidates (t : CPTTerm n) (S : Input A) (p : Polynomial ℝ) (env : Fin n → HF A) :
    t.normalizeCandidates.value S p env = stateCode
      (decodeState (t.value S p env) ∩ WitnessedChoice.edgeAtoms S) := by
  simp [normalizeCandidates]

@[simp] lemma value_normalizeRelations (t : CPTTerm n) (S : Input A) (p : Polynomial ℝ) (env : Fin n → HF A) :
    t.normalizeRelations.value S p env = ofFinset
      (((elements (t.value S p env)).image decodeRelation).image relationCode) := by
  simp [normalizeRelations]

end CPTTerm

namespace GuardedProgram

variable (G : GuardedProgram)

lemma count : G.formula.wscCount = 1 := by
  simp only [formula,Formula.wscCount,step.count,G.choice.count,G.witness.count,G.output.count]

variable (S : Input A) (p : Polynomial ℝ) (α : HF A)

lemma candidates_eq (x : Finset A) : (G.selection S p α).candidates x = G.candidateSet S p α x := by
  simp [selection,guardedSelection]

lemma candidate_edge (x : Finset A) {a : A} (h : a ∈ (G.selection S p α).candidates x) :
    a ∈ WitnessedChoice.edgeAtoms S := by
  rw [G.candidates_eq] at h
  exact (Finset.mem_inter.mp h).2

lemma witnesses_value (x : Finset A) :
    G.witnesses.value S p (Fin.cons (stateCode x) (Fin.cons α Fin.elim0)) =
      ofFinset (((G.selection S p α).witnesses x).image permutationGraph) := by
  simp only [witnesses,CPTTerm.value_letIn,CPTTerm.value_normalizeRelations,CPTTerm.value_quoted]
  convert QuotedTerm.meaning_witnessRelations S
    (Fin.cons (ofFinset ((G.cycleSet S p α x).image relationCode))
      (Fin.cons (stateCode x) (Fin.cons α Fin.elim0)))
    G.localBound .truth (.var 1) (.var 0) x (G.cycleSet S p α x) rfl rfl using 1 <;>
    simp [cycleSet,selection,guardedSelection,QuotedFormula.truth,witnessPool]

lemma choice_value (x : Finset A) :
    G.choice.value S p (Fin.cons (stateCode x) (Fin.cons α Fin.elim0)) =
      ofFinset (((G.selection S p α).choices x).image choiceCode) := by
  simp only [choice,CPTTerm.value_letIn,CPTTerm.value_normalizeCandidates,CPTTerm.value_up,
    CPTTerm.value_quoted,G.witnesses_value]
  apply QuotedTerm.meaning_guardedChoice S _ (.var 1) (.var 0) (G.selection S p α) x
  · simp only [QuotedTerm.meaning_var,Fin.cons_one]
    rw [G.candidates_eq]
    rfl
  · rfl

lemma realizes : Realizes (G.selection S p α)
    (fun x y => step.code.eval S p (Fin.cons y (Fin.cons x (Fin.cons α Fin.elim0))))
    (fun x => G.choice.code.eval S p (Fin.cons x (Fin.cons α Fin.elim0)))
    (fun z x => G.witness.code.eval S p (Fin.cons x (Fin.cons z (Fin.cons α Fin.elim0)))) := by
  constructor
  · intro x
    rw [G.choice.eval_value,G.choice_value]
  · intro x c hc
    rw [step.correct]
    apply congrArg some
    apply QuotedTerm.meaning_selectionStep S _ (.var 1) (.var 0) x c rfl rfl
    intro a ha
    subst c
    exact G.candidate_edge S p α x (Selection.some_mem_choices.mp hc).1
  · intro z x
    rw [G.witness.eval_value]
    change some ((G.witnesses.rename ![0,2]).value S p _) = _
    rw [CPTTerm.value_rename]
    have he : (Fin.cons (stateCode x) (Fin.cons (stateCode z) (Fin.cons α Fin.elim0))) ∘ ![0,2] =
        Fin.cons (stateCode x) (Fin.cons α Fin.elim0) := by
      funext i; fin_cases i <;> rfl
    rw [he,G.witnesses_value]

theorem boolean (α₀ : Fin 4 → Finset A) (hα : ∀ i, α₀ i ∈ blocks S)
    (hp : Fintype.card A+2 ≤ resource p (Fintype.card A)) :
    ∃ b : Bool, G.formula.eval S p (Fin.cons (parameterCode α₀) Fin.elim0) = some b := by
  apply (G.realizes S p (parameterCode α₀)).boolean
    (guardedSelection_filtered G.localBound S True _ _ α₀ hα)
    (resource p (Fintype.card A)) hp
  intro x
  rw [G.output.eval_value]
  simp

end GuardedProgram

end


namespace ClosedGuardedProgram

variable (G : ClosedGuardedProgram)

lemma count : G.formula.wscCount = 1 := by
  simp only [formula,Formula.existsIn,Formula.wscCount,Term.wscCount,
    G.parameterTerm.count,G.body.count,Nat.zero_add,Nat.add_zero]

variable {A : Type} [Fintype A]

lemma parameter_mem (S : Input A) (p : Polynomial ℝ) {z : HF A}
    (hz : z ∈ elements (G.parameterTerm.value S p Fin.elim0)) :
    ∃ α : Fin 4 → Finset A, (∀ i, α i ∈ WitnessedChoice.vertexBlocks S) ∧ parameterCode α = z := by
  simp only [parameterTerm,CPTTerm.value_letIn,CPTTerm.value_quoted,
    QuotedTerm.meaning_filter,elements_ofFinset,Finset.mem_filter] at hz
  exact (QuotedTerm.mem_blockParameters S _ z).mp hz.1

theorem boolean (S : Input A) (p : Polynomial ℝ)
    (hp : Fintype.card A+2 ≤ resource p (Fintype.card A)) :
    ∃ b : Bool, G.formula.eval S p Fin.elim0 = some b := by
  let bv (z : HF A) := (G.body.formula.eval S p (Fin.cons z Fin.elim0)).getD false
  have he (z : HF A) (hz : z ∈ elements (G.parameterTerm.value S p Fin.elim0)) :
      G.body.formula.eval S p (Fin.cons z Fin.elim0) = some (bv z) := by
    obtain ⟨α,hα,rfl⟩ := G.parameter_mem S p hz
    obtain ⟨b,hb⟩ := G.body.boolean S p α
      (fun i => Finset.mem_union_right _ (hα i)) hp
    simp only [bv,hb,Option.getD_some]
  refine ⟨_,Formula.eval_existsIn_on S p _ _ _ (G.parameterTerm.eval_value S p _) he⟩

theorem boolean_all (p : Polynomial ℝ) (hp : ∀ n : ℕ, n+2 ≤ resource p n) :
    (G.sentence p).BooleanOnAllInputs := by
  intro S
  exact G.boolean S.input p (hp _)

end ClosedGuardedProgram


namespace SourceProgram

open QuotedTerm QuotedFormula SourceSyntax

theorem one_occurrence : program.formula.wscCount = 1 := program.count

theorem boolean_all (p : Polynomial ℝ) (hp : ∀ n : ℕ, n+2 ≤ resource p n) :
    (program.sentence p).BooleanOnAllInputs := program.boolean_all p hp

end SourceProgram


namespace QuotedTerm

variable {n : ℕ} {A : Type} [Fintype A]

theorem closure_bound (t : QuotedTerm n) (S : Input A) (env : Fin n → HF A)
    (K : ℕ) (hK : tracePotential 0 env ≤ K) :
    (closure (t.meaning S env)).card ≤ t.code.traceBound.eval K := by
  have h : t.meaning S env = (t.code.traced S 0 env).1 := by
    have hh := (t.correct S 0 env).symm.trans (t.code.eval_traced S 0 t.count env)
    simpa only [resource,Polynomial.eval_zero,Nat.floor_zero] using Option.some.inj hh
  rw [h]
  exact (Finset.card_le_card (t.code.traced_closure S 0 env)).trans (t.code.traced_card_le S 0 env K hK)

theorem TC_bound (t : QuotedTerm n) (S : Input A) (env : Fin n → HF A)
    (K : ℕ) (hK : tracePotential 0 env ≤ K) :
    (TC (t.meaning S env)).card ≤ t.code.traceBound.eval K := by
  apply (Finset.card_le_card (show TC (t.meaning S env) ⊆ closure (t.meaning S env) from ?_)).trans
    (t.closure_bound S env K hK)
  rw [closure_eq_insert_TC]
  exact Finset.subset_insert _ _

end QuotedTerm


end WitnessedChoice.BGS

end

end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_TreeElimination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace WitnessedChoice.BGS





noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

open QuotedTerm

variable {A V : Type} [Fintype A] [Fintype V]

omit [Fintype A] [Fintype V] in
lemma ordinal_mem_elements (i j : ℕ) : ordinal (A := A) i ∈ elements (ordinal j) ↔ i<j := by
  change ordinal i ∈ ordinal (A := A) j ↔ _
  rw [mem_ordinal]
  simp only [ordinal_injective.eq_iff]
  aesop

end





end WitnessedChoice.BGS



end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_GridGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace WitnessedSeparation.Grid

noncomputable section

open Classical Support

variable {n : ℕ}

lemma epsilon_ne_zero (v : Vertex n) (e : IncidentEdges v) : epsilon v e.val ≠ 0 := by
  by_cases hh : head e.val = v
  · have ht : tail e.val ≠ v := fun h => head_ne_tail e.val (hh.trans h.symm)
    simp [epsilon,hh,ht]
  · have ht := e.property.resolve_left hh
    simp [epsilon,hh,ht]

end





noncomputable section

open Classical Support

variable {n : ℕ} {v : Vertex n} {b : Vertex n → Scalar}

lemma incident_on_axis (hn : 1 ≤ n) (v : Vertex n) (a : Fin 3) :
    ∃ e : IncidentEdges v, edgeAxis e.val = a := by
  rcases v with ⟨i,j,k⟩
  fin_cases a
  · by_cases hi : i.val = 0
    · refine ⟨⟨ex ⟨0,by omega⟩ j k,Or.inr ?_⟩,rfl⟩
      simp only [ex,tail,Prod.mk.injEq,and_true]
      apply Fin.ext
      exact hi.symm
    · refine ⟨⟨ex ⟨i.val-1,by omega⟩ j k,Or.inl ?_⟩,rfl⟩
      simp only [ex,head,Prod.mk.injEq,and_true]
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
  · by_cases hj : j.val = 0
    · refine ⟨⟨ey i ⟨0,by omega⟩ k,Or.inr ?_⟩,rfl⟩
      simp only [ey,tail,Prod.mk.injEq,true_and,and_true]
      apply Fin.ext
      exact hj.symm
    · refine ⟨⟨ey i ⟨j.val-1,by omega⟩ k,Or.inl ?_⟩,rfl⟩
      simp only [ey,head,Prod.mk.injEq,true_and,and_true]
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
  · by_cases hk : k.val = 0
    · refine ⟨⟨ez i j ⟨0,by omega⟩,Or.inr ?_⟩,rfl⟩
      simp only [ez,tail,Prod.mk.injEq,true_and]
      apply Fin.ext
      exact hk.symm
    · refine ⟨⟨ez i j ⟨k.val-1,by omega⟩,Or.inl ?_⟩,rfl⟩
      simp only [ez,head,Prod.mk.injEq,true_and]
      apply Fin.ext
      simp only [Fin.val_succ]
      omega

lemma extendVertexScalars_charge (e0 : IncidentEdges v) (z : IncidentEdges v → Scalar) :
    (∑ e, epsilon v e.val * extendVertexScalars b v e0 z e) = b v := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ e0)]
  have he : (∑ e ∈ Finset.univ.erase e0,
      epsilon v e.val * extendVertexScalars b v e0 z e) =
      ∑ e ∈ Finset.univ.erase e0, epsilon v e.val * z e := by
    apply Finset.sum_congr rfl
    intro e he
    rw [extendVertexScalars,ite_eq_right (Finset.ne_of_mem_erase he)]
  rw [he,extendVertexScalars,ite_eq_left rfl,mul_inv_cancel_left₀ (epsilon_ne_zero v e0),sub_add_cancel]

end





end WitnessedSeparation.Grid

end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_AnchoredTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace WitnessedSeparation.Grid

noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

lemma configuration_exists (hn : 1 ≤ n) (v : Vertex n) : Nonempty (Configuration b v) := by
  obtain ⟨e0,_⟩ := incident_on_axis hn v 0
  exact ⟨{ state := fun e => ⟨0,extendVertexScalars b v e0 0 e⟩
           compatible := by intro e e' f hf hf'; rfl
           charge := extendVertexScalars_charge e0 0 }⟩

lemma vertexRow_grid (v : Vertex n) (s : Configuration b v) :
    WitnessedChoice.vertexRow (atomInput b) (.inr ⟨v,s⟩) = vertexBlockSet b v := by
  ext a
  simp only [WitnessedChoice.vertexRow,WitnessedChoice.configAtoms,Finset.mem_filter,
    Finset.mem_univ,true_and,atomInput,decide_eq_true_eq,mem_vertexBlockSet]
  constructor
  · rintro ⟨_,h⟩
    cases h with | vb v s t => exact ⟨t,rfl⟩
  · rintro ⟨t,rfl⟩
    exact ⟨.cf v t,.vb v s t⟩

lemma vertexBlocks_grid (hn : 1 ≤ n) : WitnessedChoice.vertexBlocks (atomInput b) =
    Finset.univ.image (vertexBlockSet b) := by
  ext d
  simp only [WitnessedChoice.vertexBlocks,Finset.mem_image,WitnessedChoice.configAtoms,
    Finset.mem_filter,Finset.mem_univ,true_and,atomInput,decide_eq_true_eq]
  constructor
  · rintro ⟨a,h,rfl⟩
    cases h with | cf v s => exact ⟨v,(vertexRow_grid v s).symm⟩
  · rintro ⟨v,rfl⟩
    obtain ⟨s⟩ := configuration_exists (b := b) hn v
    exact ⟨.inr ⟨v,s⟩,.cf v s,vertexRow_grid v s⟩

end





noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

lemma vertex_card_le_atoms (hn : 1 ≤ n) : Fintype.card (Vertex n) ≤ Fintype.card (Atom b) := by
  let f (v : Vertex n) : Atom b := .inr ⟨v,(configuration_exists (b := b) hn v).some⟩
  apply Fintype.card_le_of_injective f
  intro v w h
  exact congrArg Sigma.fst (Sum.inr.inj h)

lemma quoted_vertexBlocks {k : ℕ} (hn : 1 ≤ n) (env : Fin k → HF (Atom b)) :
    (QuotedTerm.vertexBlocks : QuotedTerm k).meaning (atomInput b) env =
      ofFinset (Finset.univ.image (vertexCode b)) := by
  rw [QuotedTerm.meaning_vertexBlocks,vertexBlocks_grid hn,Finset.image_image]
  rfl

end





end WitnessedSeparation.Grid


end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_CycleTranslation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

namespace QuotedTerm

variable {k : ℕ} {A V : Type} [Fintype A] [Fintype V]

lemma meaning_tripleDomain (S : Input A) (env : Fin k → HF A) (VT : QuotedTerm k)
    (code : V → HF A) (hV : VT.meaning S env = ofFinset (Finset.univ.image code)) :
    (tripleDomain VT).meaning S env =
      ofFinset (Finset.univ.image (distanceCode code)) := by
  simp only [tripleDomain,meaning_bind,meaning_up,hV,elements_ofFinset,meaning_map,
    meaning_indices,meaning_triple,meaning_var,Fin.cons_zero,Fin.cons_one,fin_cons_two]
  apply ofFinset_inj.mpr
  ext z
  simp only [Finset.mem_biUnion,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨_,⟨v,rfl⟩,_,⟨w,rfl⟩,i,hi,rfl⟩
    obtain ⟨k,hk,rfl⟩ := (mem_ordinal i (Fintype.card A+1)).mp hi
    exact ⟨(v,w,⟨k,hk⟩),rfl⟩
  · rintro ⟨⟨v,w,i⟩,rfl⟩
    exact ⟨code v,⟨v,rfl⟩,code w,⟨w,rfl⟩,ordinal i.val,
      (ordinal_mem_elements _ _).mpr i.isLt,rfl⟩

end QuotedTerm

namespace SourceProgram

lemma resource_polynomial (m : ℕ) : resource polynomial m = cost.eval m := by
  unfold resource polynomial
  rw [Polynomial.eval_map]
  have h : Polynomial.eval₂ (Nat.castRingHom ℝ) (m : ℝ) cost = ((cost.eval m : ℕ) : ℝ) := by
    exact Polynomial.eval₂_at_apply (Nat.castRingHom ℝ) m
  rw [h,Nat.floor_natCast]

lemma resource_basic (m : ℕ) : m+2 ≤ resource polynomial m := by
  rw [resource_polynomial]
  simp only [cost,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_ofNat]
  omega

end SourceProgram

end

end WitnessedChoice.BGS

namespace WitnessedSeparation.Grid

noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

lemma gridResources (hn : 1 ≤ n) : GridResources SourceProgram.polynomial b := by
  refine ⟨SourceProgram.resource_basic _,?_,?_⟩
  · rw [SourceProgram.resource_polynomial]
    simp only [SourceProgram.cost,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
      Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_ofNat]
    have h := vertex_card_le_atoms (b := b) hn
    have hc : Fintype.card (BFS.Item (Vertex n) (Fintype.card (Atom b))) ≤
        Fintype.card (Atom b)^2*(Fintype.card (Atom b)+1) := by
      have h₂ := Nat.mul_le_mul_right (Fintype.card (Atom b)+1) (Nat.mul_self_le_mul_self h)
      simpa only [BFS.Item,Fintype.card_prod,Fintype.card_fin,pow_two,Nat.mul_assoc] using h₂
    omega
  · have h := QuotedTerm.TC_bound
      (QuotedTerm.tripleDomain (QuotedTerm.vertexBlocks : QuotedTerm 0))
      (atomInput b) Fin.elim0 (Fintype.card (Atom b)+1) (by simp [tracePotential])
    rw [QuotedTerm.meaning_tripleDomain _ _ _ (vertexCode b) (quoted_vertexBlocks hn _)] at h
    apply h.trans
    rw [SourceProgram.resource_polynomial]
    simp only [SourceProgram.cost,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
      Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_ofNat,Polynomial.eval_comp]
    omega

end

end WitnessedSeparation.Grid

end


end OAI
end

section
-- module Solutions.OAIQ4_WC.WitnessedChoice_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace WitnessedChoice

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Grid BGS

theorem main_oai : BGS.MainStatement := by
  let φ := SourceProgram.program.sentence SourceProgram.polynomial
  refine ⟨φ,SourceProgram.one_occurrence,
    SourceProgram.boolean_all SourceProgram.polynomial SourceProgram.resource_basic,?_⟩
  intro ψ hψ heq
  obtain ⟨n,hn,hh⟩ := ψ.agrees_on_some_grid_pair hψ
  let vstar : Vertex n := (0,0,0)
  have hzero : φ.eval (gridInput (0 : Vertex n → WitnessedSeparation.Scalar)) = some true := by
    change SourceProgram.program.formula.eval (atomInput (0 : Vertex n → WitnessedSeparation.Scalar))
      SourceProgram.polynomial Fin.elim0 = _
    rw [QuotedGrid.formula_value _ (gridResources hn) hn]
    simp
  have hone : φ.eval (gridInput (Pi.single vstar 1)) = some false := by
    change SourceProgram.program.formula.eval (atomInput (Pi.single vstar 1))
      SourceProgram.polynomial Fin.elim0 = _
    rw [QuotedGrid.formula_value _ (gridResources hn) hn]
    simp
  have hmem : gridInput (0 : Vertex n → WitnessedSeparation.Scalar) ∈ ψ.TrueModels := by
    rw [←heq]
    exact hzero
  have hmem' : gridInput (Pi.single vstar 1) ∈ φ.TrueModels := by
    rw [heq]
    exact (hh vstar).symm.trans hmem
  change φ.eval (gridInput (Pi.single vstar 1)) = some true at hmem'
  rw [hone] at hmem'
  contradiction

end

end WitnessedChoice

end OAI
end

theorem solution : type_of% @OAI.WitnessedChoice.main_oai := @OAI.WitnessedChoice.main_oai
