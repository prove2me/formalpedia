-- Prove2me | solution 1 for TensorNP.SpectralNorm.lemma_6_11
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T05:11:16.825034+00:00
-- url     : https://prove2.me/submissions/06868806-a67b-4875-a594-07624a95e564

import Theorems.Thm_TensorNP_SpectralNorm_display_22
import Theorems.Thm_TensorNP_SpectralNorm_lemma_6_8
import Theorems.Thm_TensorNP_SpectralNorm_proposition_6_10
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_TensorNP_SpectralNorm_Tensor
import Definitions.Def_TensorNP_SpectralNorm_CliqueTensor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Fin


open scoped BigOperators
open TensorNP.SpectralNorm Matrix

namespace SpectralCompact

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

noncomputable def B {m n : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (u v : E n) : E m :=
  WithLp.toLp 2 fun k => u ⬝ᵥ (A k *ᵥ v)

lemma norm_eq_l2 {n : ℕ} (u : E n) : ‖u‖ = TensorNP.SpectralNorm.l2norm u := by
  simpa [TensorNP.SpectralNorm.l2norm] using EuclideanSpace.norm_eq u

lemma norm_B_sq {m n : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (u v : E n) :
    ‖B A u v‖^2 = ∑ k, (u ⬝ᵥ (A k *ᵥ v))^2 := by
  exact EuclideanSpace.real_norm_sq_eq (B A u v)

lemma continuous_diagonal {m n : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) :
    Continuous (fun z : E n => ‖B A z z‖) := by
  unfold B
  fun_prop

open TensorNP.SpectralNorm

lemma continuous_mixed {m n : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) :
    Continuous (fun p : E n × E n => ‖B A p.1 p.2‖^2) := by
  unfold B
  fun_prop

lemma mixed_bddAbove {m n : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) :
    BddAbove {t : ℝ | ∃ u v : Fin n → ℝ, l2norm u = 1 ∧ l2norm v = 1 ∧
        t = ∑ k, (u ⬝ᵥ (A k *ᵥ v)) ^ 2} := by
  have hc := (isCompact_sphere (0 : E n) 1).prod (isCompact_sphere (0 : E n) 1)
  apply (hc.image (continuous_mixed A)).bddAbove.mono
  rintro t ⟨u, v, hu, hv, rfl⟩
  exact ⟨(WithLp.toLp 2 u, WithLp.toLp 2 v),
    ⟨mem_sphere_zero_iff_norm.mpr ((norm_eq_l2 _).trans hu),
      mem_sphere_zero_iff_norm.mpr ((norm_eq_l2 _).trans hv)⟩, norm_B_sq A _ _⟩

lemma diagonal_attains {m n : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (hn : 0 < n) :
    ∃ u : Fin n → ℝ, l2norm u = 1 ∧
      (∑ k, (u ⬝ᵥ (A k *ᵥ u)) ^ 2) =
        sSup {t : ℝ | ∃ v : Fin n → ℝ, l2norm v = 1 ∧
          t = ∑ k, (v ⬝ᵥ (A k *ᵥ v)) ^ 2} := by
  have : NeZero n := ⟨ne_of_gt hn⟩
  obtain ⟨y, hy, hmax⟩ := (isCompact_sphere (0 : E n) 1).exists_isMaxOn
    (NormedSpace.sphere_nonempty.mpr zero_le_one) (continuous_diagonal A).continuousOn
  have hy2 : l2norm y = 1 := (norm_eq_l2 y).symm.trans (mem_sphere_zero_iff_norm.mp hy)
  have hg : IsGreatest {t : ℝ | ∃ v : Fin n → ℝ, l2norm v = 1 ∧
      t = ∑ k, (v ⬝ᵥ (A k *ᵥ v)) ^ 2} (∑ k, (y ⬝ᵥ (A k *ᵥ y))^2) := by
    refine ⟨⟨y, hy2, rfl⟩, ?_⟩
    rintro t ⟨v, hv, rfl⟩
    simpa only [norm_B_sq] using (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
      (hmax (mem_sphere_zero_iff_norm.mpr ((norm_eq_l2 (WithLp.toLp 2 v)).trans hv)))
  exact ⟨y, hy2, hg.csSup_eq.symm⟩

end SpectralCompact


private def catVec {α : Type} {l e : ℕ} (a : Fin l → α) (b c : Fin e → α) :
    Fin (l + 2 * e) → α :=
  (Fin.append (Fin.append a b) c) ∘ Fin.cast (by omega)

private theorem sum_blocks {l e : ℕ} (f : Fin (l + 2 * e) → ℝ) :
    (∑ i, f i) =
      (∑ i : Fin l, f ⟨i.val, by omega⟩) +
      (∑ k : Fin e, f ⟨l + k.val, by omega⟩) +
      (∑ k : Fin e, f ⟨e + l + k.val, by omega⟩) := by
  have h := (finCongr (by omega : (l + e) + e = l + 2 * e)).sum_comp f
  simpa [Fin.sum_univ_add, finCongr, Fin.cast, Fin.castAdd, Fin.natAdd, Nat.add_comm e l] using h.symm

private theorem catVec_left {α : Type} {l e : ℕ} (a : Fin l → α) (b c : Fin e → α)
    (i : Fin l) : catVec a b c ⟨i.val, by omega⟩ = a i := by
  change (Fin.append (Fin.append a b) c) (Fin.castAdd e (Fin.castAdd e i)) = a i
  simp only [Fin.append_left]

private theorem catVec_middle {α : Type} {l e : ℕ} (a : Fin l → α) (b c : Fin e → α)
    (k : Fin e) : catVec a b c ⟨l + k.val, by omega⟩ = b k := by
  exact (Fin.append_left (Fin.append a b) c (Fin.natAdd l k)).trans (Fin.append_right a b k)

private theorem catVec_right {α : Type} {l e : ℕ} (a : Fin l → α) (b c : Fin e → α)
    (k : Fin e) : catVec a b c ⟨e + l + k.val, by omega⟩ = c k := by
  simpa [catVec, Fin.cast, Fin.natAdd, Nat.add_comm e l] using
    Fin.append_right (Fin.append a b) c k

private theorem sum_catVec {α : Type} {l e : ℕ} (a : Fin l → α) (b c : Fin e → α)
    (f : α → ℝ) :
    (∑ i, f (catVec a b c i)) = (∑ i, f (a i)) + (∑ k, f (b k)) + (∑ k, f (c k)) := by
  rw [sum_blocks]
  simp only [catVec_left, catVec_middle, catVec_right]

private theorem append_forall {α : Type} {l e : ℕ} (a : Fin l → α) (b : Fin e → α)
    (P : α → Prop) (ha : ∀ i, P (a i)) (hb : ∀ k, P (b k)) (j : Fin (l + e)) :
    P (Fin.append a b j) := by
  exact Fin.addCases
    (fun i => (Fin.append_left a b i).symm ▸ ha i)
    (fun k => (Fin.append_right a b k).symm ▸ hb k) j

private theorem catVec_forall {α : Type} {l e : ℕ} (a : Fin l → α) (b c : Fin e → α)
    (P : α → Prop) (ha : ∀ i, P (a i)) (hb : ∀ k, P (b k)) (hc : ∀ k, P (c k))
    (j : Fin (l + 2 * e)) : P (catVec a b c j) := by
  exact append_forall (Fin.append a b) c P (append_forall a b P ha hb) hc
    (Fin.cast (by omega) j)

private noncomputable def mats {v e : ℕ} (G : SimpleGraph (Fin v))
    (ε : Fin e ≃ G.edgeSet) (l : ℕ) : Fin (l + 2 * e) → Matrix (Fin v) (Fin v) ℝ :=
  catVec (fun _ : Fin l => (1 / (l : ℝ)) • (1 : Matrix (Fin v) (Fin v) ℝ))
    (fun k => edgeMatrix ℝ (ε k : Sym2 (Fin v)))
    (fun k => edgeMatrix ℝ (ε k : Sym2 (Fin v)))

private theorem sum_mats_sq {v e : ℕ} (G : SimpleGraph (Fin v))
    (ε : Fin e ≃ G.edgeSet) (l : ℕ) (x y : Fin v → ℝ) :
    (∑ i, (x ⬝ᵥ ((mats G ε l i) *ᵥ y)) ^ 2) =
      (∑ _i : Fin l, (x ⬝ᵥ (((1 / (l : ℝ)) • (1 : Matrix (Fin v) (Fin v) ℝ)) *ᵥ y)) ^ 2) +
        2 * ∑ k : Fin e, (x ⬝ᵥ (edgeMatrix ℝ (ε k : Sym2 (Fin v)) *ᵥ y)) ^ 2 := by
  simpa only [mats, two_mul, add_assoc] using
    sum_catVec
      (fun _ : Fin l => (1 / (l : ℝ)) • (1 : Matrix (Fin v) (Fin v) ℝ))
      (fun k => edgeMatrix ℝ (ε k : Sym2 (Fin v)))
      (fun k => edgeMatrix ℝ (ε k : Sym2 (Fin v)))
      (fun M => (x ⬝ᵥ (M *ᵥ y)) ^ 2)

private theorem form_eq_dot {v e : ℕ} (G : SimpleGraph (Fin v))
    (ε : Fin e ≃ G.edgeSet) (l : ℕ) (x y : Fin v → ℝ) (w : Fin (l + 2 * e) → ℝ) :
    form26 G ε l x y w = (fun i => x ⬝ᵥ ((mats G ε l i) *ᵥ y)) ⬝ᵥ w := by
  simpa only [form26, dotProduct, mats, catVec_left, catVec_middle, catVec_right] using
    (sum_blocks (fun i => (x ⬝ᵥ ((mats G ε l i) *ᵥ y)) * w i)).symm

private theorem edge_symm {v : ℕ} (s : Sym2 (Fin v)) : (edgeMatrix ℝ s).IsSymm := by
  ext i j
  simp only [edgeMatrix, Matrix.transpose_apply, Matrix.of_apply, Sym2.eq_swap]

private theorem mats_symm {v e : ℕ} (G : SimpleGraph (Fin v))
    (ε : Fin e ≃ G.edgeSet) (l : ℕ) : ∀ i, (mats G ε l i).IsSymm := by
  exact catVec_forall _ _ _ Matrix.IsSymm
    (fun _ => Matrix.isSymm_one.smul (1 / (l : ℝ)))
    (fun k => edge_symm (ε k : Sym2 (Fin v))) (fun k => edge_symm (ε k : Sym2 (Fin v)))

private theorem dot_upper {n : ℕ} (c w : Fin n → ℝ) (hw : l2norm w = 1) :
    c ⬝ᵥ w ≤ l2norm c := by
  have h : c ⬝ᵥ w ≤ l2norm c * l2norm w := by
    simpa only [dotProduct, l2norm] using Real.sum_mul_le_sqrt_mul_sqrt Finset.univ c w
  simpa only [hw, mul_one] using h

private theorem dot_attain {n : ℕ} (c : Fin n → ℝ) (hc : 0 < l2norm c) :
    ∃ w : Fin n → ℝ, l2norm w = 1 ∧ c ⬝ᵥ w = l2norm c := by
  have hs : l2norm c ^ 2 = ∑ i, c i ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  refine ⟨fun i => c i / l2norm c, ?_, ?_⟩
  · apply Real.sqrt_eq_one.mpr
    simp only [div_pow]
    simp only [div_eq_mul_inv, ← Finset.sum_mul, ← hs]
    exact mul_inv_cancel₀ (pow_ne_zero 2 hc.ne')
  · simp only [dotProduct, ← mul_div_assoc, ← sq]
    simp only [div_eq_mul_inv, ← Finset.sum_mul, ← hs]
    simp [sq, hc.ne']

private theorem norm_first {v : ℕ} (l : ℕ) (hl : 1 ≤ l) (u : Fin v → ℝ)
    (hu : l2norm u = 1) :
    (∑ _i : Fin l, (u ⬝ᵥ (((1 / (l : ℝ)) • (1 : Matrix (Fin v) (Fin v) ℝ)) *ᵥ u)) ^ 2) =
      1 / (l : ℝ) := by
  have hs : (∑ i, u i ^ 2) = 1 := Real.sqrt_eq_one.mp hu
  simp_rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul]
  simp [dotProduct, ← sq, hs]
  field_simp


private theorem diagonal_sup {v e : ℕ} (G : SimpleGraph (Fin v))
    (ε : Fin e ≃ G.edgeSet) (l : ℕ) :
    sSup {t : ℝ | ∃ u : Fin v → ℝ, l2norm u = 1 ∧
      t = ∑ i, (u ⬝ᵥ ((mats G ε l i) *ᵥ u)) ^ 2} = Nval G ε l := by
  unfold Nval
  apply congrArg sSup
  ext t
  simp only [Set.mem_ofPred_eq, Set.mem_image, sum_mats_sq, eq_comm]

private theorem mixed_sup {v e : ℕ} (hv : 0 < v) (G : SimpleGraph (Fin v))
    [DecidableRel G.Adj] (ε : Fin e ≃ G.edgeSet) (l : ℕ) (hl : 1 ≤ l) :
    sSup {t : ℝ | ∃ x y : Fin v → ℝ, l2norm x = 1 ∧ l2norm y = 1 ∧
      t = ∑ i, (x ⬝ᵥ ((mats G ε l i) *ᵥ y)) ^ 2} = Mval G l := by
  exact (proposition_6_10 (mats G ε l) (mats_symm G ε l)).trans
    ((diagonal_sup G ε l).trans (lemma_6_8 hv G ε l hl).symm)

private theorem diagonal_M_attains {v e : ℕ} (hv : 0 < v) (G : SimpleGraph (Fin v))
    [DecidableRel G.Adj] (ε : Fin e ≃ G.edgeSet) (l : ℕ) (hl : 1 ≤ l) :
    ∃ u : Fin v → ℝ, l2norm u = 1 ∧
      (∑ i, (u ⬝ᵥ ((mats G ε l i) *ᵥ u)) ^ 2) = Mval G l := by
  exact (SpectralCompact.diagonal_attains (mats G ε l) hv).imp fun u hu =>
    ⟨hu.1, hu.2.trans ((diagonal_sup G ε l).trans (lemma_6_8 hv G ε l hl).symm)⟩

private theorem diagonal_score_pos {v e : ℕ} (G : SimpleGraph (Fin v))
    (ε : Fin e ≃ G.edgeSet) (l : ℕ) (hl : 1 ≤ l) (u : Fin v → ℝ)
    (hu : l2norm u = 1) : 0 < ∑ i, (u ⬝ᵥ ((mats G ε l i) *ᵥ u)) ^ 2 := by
  rw [sum_mats_sq, norm_first l hl u hu]
  exact add_pos_of_pos_of_nonneg
    (one_div_pos.mpr (Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hl)))
    (mul_nonneg zero_le_two (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

private theorem form_upper {v e : ℕ} (hv : 0 < v) (G : SimpleGraph (Fin v))
    [DecidableRel G.Adj] (ε : Fin e ≃ G.edgeSet) (l : ℕ) (hl : 1 ≤ l)
    (x y : Fin v → ℝ) (w : Fin (l + 2 * e) → ℝ)
    (hx : l2norm x = 1) (hy : l2norm y = 1) (hw : l2norm w = 1) :
    form26 G ε l x y w ≤ Real.sqrt (Mval G l) := by
  rw [form_eq_dot]
  refine (dot_upper _ w hw).trans ?_
  exact Real.sqrt_le_sqrt
    ((le_csSup (SpectralCompact.mixed_bddAbove (mats G ε l)) ⟨x, y, hx, hy, rfl⟩).trans_eq
      (mixed_sup hv G ε l hl))

private theorem T_greatest {v e : ℕ} (hv : 0 < v) (G : SimpleGraph (Fin v))
    [DecidableRel G.Adj] (ε : Fin e ≃ G.edgeSet) (l : ℕ) (hl : 1 ≤ l) :
    IsGreatest {t : ℝ | ∃ (x y : Fin v → ℝ) (w : Fin (l + 2 * e) → ℝ),
      l2norm x = 1 ∧ l2norm y = 1 ∧ l2norm w = 1 ∧ t = form26 G ε l x y w}
      (Real.sqrt (Mval G l)) := by
  obtain ⟨u, hu, hMu⟩ := diagonal_M_attains hv G ε l hl
  have hc : 0 < l2norm (fun i => u ⬝ᵥ ((mats G ε l i) *ᵥ u)) :=
    Real.sqrt_pos.mpr (diagonal_score_pos G ε l hl u hu)
  obtain ⟨w, hw, hcw⟩ := dot_attain _ hc
  refine ⟨⟨u, u, w, hu, hu, hw,
    ((form_eq_dot G ε l u u w).trans (hcw.trans (congrArg Real.sqrt hMu))).symm⟩, ?_⟩
  rintro t ⟨x, y, z, hx, hy, hz, rfl⟩
  exact form_upper hv G ε l hl x y z hx hy hz

private theorem comparison_iffs (a b : ℕ) (r : ℝ)
    (heq : a = b → r = 1) (hlt : a < b → 1 < r) (hgt : b < a → r < 1) :
    (r = 1 ↔ a = b) ∧ (1 < r ↔ a < b) ∧ (r < 1 ↔ b < a) := by
  grind

theorem solution {v e : ℕ} (hv : 0 < v) (G : SimpleGraph (Fin v)) [DecidableRel G.Adj]
    (ε : Fin e ≃ G.edgeSet) (l : ℕ) (hl : 1 ≤ l) :
    Tval G ε l = Real.sqrt (Mval G l) ∧
      (Tval G ε l = 1 ↔ l = G.cliqueNum) ∧
      (1 < Tval G ε l ↔ l < G.cliqueNum) ∧
      (Tval G ε l < 1 ↔ G.cliqueNum < l) := by
  have hT : Tval G ε l = Real.sqrt (Mval G l) := (T_greatest hv G ε l hl).csSup_eq
  have hd := (display_22 hv G l hl).2.2
  have hm := comparison_iffs l G.cliqueNum (Mval G l) hd.1 hd.2.1 hd.2.2
  simpa only [hT, Real.sqrt_eq_one, Real.lt_sqrt zero_le_one,
    Real.sqrt_lt' zero_lt_one, one_pow] using And.intro hT hm
