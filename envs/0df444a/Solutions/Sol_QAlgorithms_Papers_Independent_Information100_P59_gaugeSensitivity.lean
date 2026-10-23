-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P59.gaugeSensitivity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:31:33.531641+00:00
-- url     : https://prove2.me/submissions/8f8e19c4-58f5-4752-b2ff-ca7e29ede086

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P59
noncomputable section
open scoped Matrix ComplexOrder

namespace X4P59G
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P59
attribute [local instance 100] LieRing.ofAssociativeRing

def g0 : Block := !![0, (-1:ℝ), 0, 0; 1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]
def g1 : Block := !![(-1/2:ℝ), 0, (3/5:ℝ), 0; 0, (-1/2:ℝ), 0, 0; (-3/5:ℝ), 0, (-1:ℝ), (-1:ℝ); 0, 0, 0, 0]
def g2 : Block := !![0, 0, 0, 0; 0, 0, (3/5:ℝ), 0; 0, (-3/5:ℝ), 0, 0; 0, 0, 0, 0]
def g3 : Block := !![0, 0, (3/5:ℝ), 0; 0, 0, 0, 0; (-3/5:ℝ), 0, 0, 0; 0, 0, 0, 0]
def g4 : Block := !![0, (9/25:ℝ), 0, 0; (-9/25:ℝ), 0, (-3/10:ℝ), (-3/5:ℝ); 0, (-3/10:ℝ), 0, 0; 0, 0, 0, 0]
def g5 : Block := !![0, 0, (-3/10:ℝ), (-3/5:ℝ); 0, 0, 0, 0; (-3/10:ℝ), 0, 0, 0; 0, 0, 0, 0]
def g6 : Block := !![0, (9/50:ℝ), 0, 0; (9/50:ℝ), 0, (-33/500:ℝ), 0; 0, (33/500:ℝ), 0, 0; 0, 0, 0, 0]
def g7 : Block := !![(9/25:ℝ), 0, (3/20:ℝ), 0; 0, 0, 0, 0; (-3/20:ℝ), 0, (-9/25:ℝ), (-9/25:ℝ); 0, 0, 0, 0]
def g8 : Block := !![(9/25:ℝ), 0, (-33/500:ℝ), 0; 0, (-9/25:ℝ), 0, 0; (33/500:ℝ), 0, 0, 0; 0, 0, 0, 0]
def g9 : Block := !![0, (-99/2500:ℝ), 0, 0; (99/2500:ℝ), 0, (141/1000:ℝ), (33/500:ℝ); 0, (141/1000:ℝ), 0, 0; 0, 0, 0, 0]
def g10 : Block := !![0, 0, (357/1000:ℝ), (33/500:ℝ); 0, 0, 0, 0; (357/1000:ℝ), 0, 0, 0; 0, 0, 0, 0]
def g11 : Block := !![(-1071/2500:ℝ), 0, (-357/2000:ℝ), (-81/250:ℝ); 0, 0, 0, 0; (357/2000:ℝ), 0, (1071/2500:ℝ), (99/2500:ℝ); 0, 0, 0, 0]

lemma g0_eq : controlBlock ![0,0,1] = g0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [controlBlock, affineBlock, rotationGenerator, g0]

lemma g1_eq : shiftedDamping (3/5) = g1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [shiftedDamping, dampingBlock, controlBlock, affineBlock, rotationGenerator, g1] <;> norm_num

lemma br2 : ⁅g0, g1⁆ = g2 := by
  rw [Ring.lie_def]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [g0, g1, g2, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num

lemma br3 : ⁅g2, g0⁆ = g3 := by
  rw [Ring.lie_def]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [g2, g0, g3, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num

lemma br4 : ⁅g2, g1⁆ = g4 := by
  rw [Ring.lie_def]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [g2, g1, g4, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num

lemma br5 : ⁅g3, g1⁆ = g5 := by
  rw [Ring.lie_def]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [g3, g1, g5, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num

lemma br6 : ⁅g4, g1⁆ = g6 := by
  rw [Ring.lie_def]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [g4, g1, g6, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num

lemma br7 : ⁅g5, g1⁆ = g7 := by
  rw [Ring.lie_def]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [g5, g1, g7, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num

lemma br8 : ⁅g6, g0⁆ = g8 := by
  rw [Ring.lie_def]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [g6, g0, g8, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num

lemma br9 : ⁅g6, g1⁆ = g9 := by
  rw [Ring.lie_def]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [g6, g1, g9, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num

lemma br10 : ⁅g7, g1⁆ = g10 := by
  rw [Ring.lie_def]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [g7, g1, g10, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num

lemma br11 : ⁅g10, g1⁆ = g11 := by
  rw [Ring.lie_def]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [g10, g1, g11, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num

abbrev LS : LieSubalgebra ℝ Block :=
  LieSubalgebra.lieSpan ℝ Block {controlBlock ![0,0,1], shiftedDamping (3/5)}

lemma mem0 : g0 ∈ LS := g0_eq ▸ LieSubalgebra.subset_lieSpan (Set.mem_insert _ _)
lemma mem1 : g1 ∈ LS := g1_eq ▸ LieSubalgebra.subset_lieSpan (Set.mem_insert_of_mem _ rfl)
lemma mem2 : g2 ∈ LS := br2 ▸ LS.lie_mem mem0 mem1
lemma mem3 : g3 ∈ LS := br3 ▸ LS.lie_mem mem2 mem0
lemma mem4 : g4 ∈ LS := br4 ▸ LS.lie_mem mem2 mem1
lemma mem5 : g5 ∈ LS := br5 ▸ LS.lie_mem mem3 mem1
lemma mem6 : g6 ∈ LS := br6 ▸ LS.lie_mem mem4 mem1
lemma mem7 : g7 ∈ LS := br7 ▸ LS.lie_mem mem5 mem1
lemma mem8 : g8 ∈ LS := br8 ▸ LS.lie_mem mem6 mem0
lemma mem9 : g9 ∈ LS := br9 ▸ LS.lie_mem mem6 mem1
lemma mem10 : g10 ∈ LS := br10 ▸ LS.lie_mem mem7 mem1
lemma mem11 : g11 ∈ LS := br11 ▸ LS.lie_mem mem10 mem1

def gv : Fin 12 → Block := ![g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11]

lemma gv_li : LinearIndependent ℝ gv := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have E : ∀ a b, (∑ i, c i • gv i) a b = 0 := fun a b => by rw [hc]; rfl
  have e00 := E 0 0
  have e01 := E 0 1
  have e02 := E 0 2
  have e03 := E 0 3
  have e10 := E 1 0
  have e11 := E 1 1
  have e12 := E 1 2
  have e13 := E 1 3
  have e20 := E 2 0
  have e21 := E 2 1
  have e22 := E 2 2
  have e23 := E 2 3
  simp [Fin.sum_univ_succ, gv, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, Matrix.sum_apply] at e00 e01 e02 e03 e10 e11 e12 e13 e20 e21 e22 e23
  intro i
  fin_cases i <;> simp <;> linarith

end X4P59G

noncomputable section
open scoped Matrix ComplexOrder

namespace X4P59G
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P59
attribute [local instance 100] LieRing.ofAssociativeRing

def LRZ : LieSubalgebra ℝ Block where
  carrier := {X | ∀ j, X 3 j = 0}
  add_mem' := by intro a b ha hb j; simp [ha j, hb j]
  zero_mem' := by intro j; simp
  smul_mem' := by intro c a ha j; simp [ha j]
  lie_mem' := by
    intro a b ha hb j
    simp only [Set.mem_setOf_eq] at ha hb
    simp [Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, ha, hb]

def u : Fin 3 × Fin 4 → Block := fun p => Matrix.single p.1.castSucc p.2 1

lemma LRZ_le : LRZ.toSubmodule ≤ Submodule.span ℝ (Set.range u) := by
  intro X hX
  have hX' : ∀ j, X 3 j = 0 := hX
  have e : X = ∑ p, X p.1.castSucc p.2 • u p := by
    ext a b
    simp only [Matrix.sum_apply, Matrix.smul_apply, u, Matrix.single_apply, Fintype.sum_prod_type,
      Fin.sum_univ_three, Fin.sum_univ_four]
    fin_cases a <;> fin_cases b <;> simp [hX']
  rw [e]
  exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)

lemma LS_le : LS ≤ LRZ := by
  rw [LieSubalgebra.lieSpan_le]
  intro X hX
  rcases hX with rfl | rfl
  · rw [g0_eq]; intro j; fin_cases j <;> simp [g0]
  · rw [g1_eq]; intro j; fin_cases j <;> simp [g1]

lemma finrank_LS : Module.finrank ℝ LS = 12 := by
  apply le_antisymm
  · have h1 : LS.toSubmodule ≤ Submodule.span ℝ (Set.range u) :=
      le_trans (fun x hx => LS_le hx) LRZ_le
    have h2 := Submodule.finrank_mono h1
    have h3 := finrank_range_le_card (R := ℝ) u
    simp at h3
    exact le_trans h2 h3
  · have mem : ∀ i, gv i ∈ LS := by
      intro i
      fin_cases i
      exacts [mem0, mem1, mem2, mem3, mem4, mem5, mem6, mem7, mem8, mem9, mem10, mem11]
    let f : Fin 12 → LS := fun i => ⟨gv i, mem i⟩
    have hf : LinearIndependent ℝ f := by
      apply LinearIndependent.of_comp (LS.toSubmodule.subtype)
      exact gv_li
    have := hf.fintype_card_le_finrank
    simpa using this

/-! dimension 2 -/

abbrev LS2 : LieSubalgebra ℝ Block :=
  LieSubalgebra.lieSpan ℝ Block {controlBlock ![0,0,1], dampingBlock}

def d1 : Block := !![(-1/2:ℝ), 0, 0, 0; 0, (-1/2:ℝ), 0, 0; 0, 0, (-1:ℝ), (-1:ℝ); 0, 0, 0, 0]

lemma d1_eq : dampingBlock = d1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [dampingBlock, affineBlock, d1] <;> norm_num

lemma comm01 : g0 * d1 = d1 * g0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [g0, d1, Matrix.mul_apply, Fin.sum_univ_four]

def P2 : LieSubalgebra ℝ Block where
  carrier := Submodule.span ℝ {g0, d1}
  add_mem' := Submodule.add_mem _
  zero_mem' := Submodule.zero_mem _
  smul_mem' := fun c _ h => Submodule.smul_mem _ c h
  lie_mem' := by
    intro x y hx hy
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
    obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hy
    have : ⁅a • g0 + b • d1, c • g0 + d • d1⁆ = 0 := by
      rw [Ring.lie_def]
      simp only [add_mul, mul_add, smul_mul_smul_comm, comm01]
      module
    rw [this]; exact Submodule.zero_mem _

lemma finrank_LS2 : Module.finrank ℝ LS2 = 2 := by
  have mem0' : g0 ∈ LS2 := g0_eq ▸ LieSubalgebra.subset_lieSpan (Set.mem_insert _ _)
  have mem1' : d1 ∈ LS2 := d1_eq ▸ LieSubalgebra.subset_lieSpan (Set.mem_insert_of_mem _ rfl)
  apply le_antisymm
  · have hle : LS2 ≤ P2 := by
      rw [LieSubalgebra.lieSpan_le]
      intro X hX
      rcases hX with rfl | rfl
      · rw [g0_eq]; exact Submodule.subset_span (Set.mem_insert _ _)
      · rw [d1_eq]; exact Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
    have h1 : LS2.toSubmodule ≤ Submodule.span ℝ (Set.range ![g0, d1]) := by
      have : LS2.toSubmodule ≤ Submodule.span ℝ {g0, d1} := fun x hx => hle hx
      convert this using 2
      ext x; simp [Fin.exists_fin_two]; tauto
    have h3 := finrank_range_le_card (R := ℝ) ![g0, d1]
    rw [Fintype.card_fin] at h3
    exact le_trans (Submodule.finrank_mono h1) h3
  · let f : Fin 2 → LS2 := ![⟨g0, mem0'⟩, ⟨d1, mem1'⟩]
    have hf : LinearIndependent ℝ f := by
      apply LinearIndependent.of_comp (LS2.toSubmodule.subtype)
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      have e1 := congrFun (congrFun hc 1) 0
      have e2 := congrFun (congrFun hc 1) 1
      simp [f, Fin.sum_univ_two, g0, d1] at e1 e2
      fin_cases i <;> simp <;> linarith
    have := hf.fintype_card_le_finrank
    simpa using this

end X4P59G

noncomputable section
open scoped Matrix ComplexOrder

namespace X4P59G
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P59

lemma gauge {d : ℕ} (hd : 0 < d) (L H : Matrix (Fin d) (Fin d) ℂ) (c : ℂ) (hH : H.IsHermitian) :
    (gaugeHamiltonian L c).IsHermitian ∧
    (∀ X, coherent H X + dissipator L X =
      coherent (H - gaugeHamiltonian L c) X + dissipator (L + c • 1) X) ∧
    (L.trace = 0 → c ≠ 0 → (L + c • 1).trace ≠ 0) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold gaugeHamiltonian Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_conjTranspose]
    simp only [star_div₀, Complex.star_def, Complex.conj_I, star_star, map_ofNat, Complex.conj_conj]
    rw [smul_sub, smul_sub, neg_div, neg_smul, neg_smul]
    abel
  · intro X
    unfold coherent dissipator gaugeHamiltonian
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, smul_sub, smul_add, smul_smul]
    match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring
  · intro hL hc
    rw [Matrix.trace_add, hL, zero_add, Matrix.trace_smul, Matrix.trace_one]
    simp [hc, hd.ne']

end X4P59G

section
open QAlgorithms.Papers.Independent.Information100.P59
attribute [local instance 100] LieRing.ofAssociativeRing

theorem solution :
    (∀ {d : ℕ}, 0 < d → ∀ (L H : Matrix (Fin d) (Fin d) ℂ) (c : ℂ),
      H.IsHermitian →
      (gaugeHamiltonian L c).IsHermitian ∧
      (∀ X, coherent H X + dissipator L X =
        coherent (H - gaugeHamiltonian L c) X + dissipator (L + c • 1) X) ∧
      (L.trace = 0 → c ≠ 0 → (L + c • 1).trace ≠ 0)) ∧
    Module.finrank ℝ (LieSubalgebra.lieSpan ℝ Block
      {controlBlock ![0,0,1], dampingBlock}) = 2 ∧
    Module.finrank ℝ (LieSubalgebra.lieSpan ℝ Block
      {controlBlock ![0,0,1], shiftedDamping (3/5)}) = 12 :=
  ⟨fun hd L H c hH => X4P59G.gauge hd L H c hH, X4P59G.finrank_LS2, X4P59G.finrank_LS⟩

end
