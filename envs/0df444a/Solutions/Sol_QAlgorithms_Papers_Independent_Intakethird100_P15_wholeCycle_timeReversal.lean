-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P15.wholeCycle_timeReversal
-- status  : ACCEPTED   (prove)
-- author  : @Yivy Yu
-- created : 2026-11-14T02:09:53.790447+00:00
-- url     : https://prove2.me/submissions/59073cd1-5fc3-42b0-9b2a-891d4ade5c83

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P15

open Filter MeasureTheory
open QAlgorithms.Papers.Independent.Intakethird100.P15
open scoped Topology

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type v} {Ω : Type w} [MeasurableSpace Ω]

omit [CompleteSpace E] in
private theorem inner_symm_apply (U : E ≃ₗᵢ[ℂ] E) (x y : E) :
    inner ℂ (U.symm x) y = inner ℂ x (U y) := by
  rw [← U.inner_map_map (U.symm x) y, U.apply_symm_apply]

omit [CompleteSpace E] in
private theorem spectralStep_symmetric
    {b : HilbertBasis ι ℂ E} {H : RealSpectralHamiltonian (Ω := Ω) b}
    {tau hbar : ℝ} {U : E ≃ₗᵢ[ℂ] E} (h : IsSpectralStep b H tau hbar U) (i j : ι) :
    inner ℂ (b i) (U (b j)) = inner ℂ (b j) (U (b i)) := by
  rw [h (b i) (b j), h (b j) (b i)]
  apply integral_congr_ae
  filter_upwards [H.real_basis i, H.real_basis j] with s hi hj
  have hreal_i : star (H.transform (b i) s) = H.transform (b i) s :=
    Complex.conj_eq_iff_im.mpr hi
  have hreal_j : star (H.transform (b j) s) = H.transform (b j) s :=
    Complex.conj_eq_iff_im.mpr hj
  rw [hreal_i, hreal_j]
  ring

omit [CompleteSpace E] in
private theorem spectralStep_unique
    {b : HilbertBasis ι ℂ E} {H : RealSpectralHamiltonian (Ω := Ω) b}
    {tau hbar : ℝ} {U V : E ≃ₗᵢ[ℂ] E}
    (hU : IsSpectralStep b H tau hbar U) (hV : IsSpectralStep b H tau hbar V) :
    U = V := by
  ext y
  apply ext_inner_left ℂ
  intro x
  rw [hU x y, hV x y]

omit [CompleteSpace E] in
private theorem trans_entry (b : HilbertBasis ι ℂ E) (A B : E ≃ₗᵢ[ℂ] E) (i j : ι) :
    inner ℂ (b i) ((A.trans B) (b j)) =
      ∑' k : ι, inner ℂ (b i) (B (b k)) * inner ℂ (b k) (A (b j)) := by
  change inner ℂ (b i) (B (A (b j))) = _
  rw [← inner_symm_apply B (b i) (A (b j)), ← b.tsum_inner_mul_inner]
  exact tsum_congr fun k => by rw [inner_symm_apply]

omit [CompleteSpace E] in
private theorem trans_transposes (b : HilbertBasis ι ℂ E) {A A' B B' : E ≃ₗᵢ[ℂ] E}
    (hA : ∀ i j, inner ℂ (b i) (A (b j)) = inner ℂ (b j) (A' (b i)))
    (hB : ∀ i j, inner ℂ (b i) (B (b j)) = inner ℂ (b j) (B' (b i)))
    (i j : ι) :
    inner ℂ (b i) ((A.trans B) (b j)) = inner ℂ (b j) ((B'.trans A') (b i)) := by
  rw [trans_entry, trans_entry]
  exact tsum_congr fun k => by rw [hB i k, hA k j, mul_comm]

omit [CompleteSpace E] in
private theorem foldl_trans (L : List (E ≃ₗᵢ[ℂ] E)) (A : E ≃ₗᵢ[ℂ] E) :
    L.foldl (fun U V => U.trans V) A = A.trans (chronologicalEvolution L) := by
  induction L generalizing A with
  | nil => simp [chronologicalEvolution]
  | cons V L ih =>
    simp only [List.foldl_cons, chronologicalEvolution, LinearIsometryEquiv.refl_trans]
    change L.foldl (fun U V => U.trans V) (A.trans V) =
      A.trans (L.foldl (fun U V => U.trans V) V)
    rw [ih, ih, LinearIsometryEquiv.trans_assoc]

omit [CompleteSpace E] in
private theorem evolution_cons (A : E ≃ₗᵢ[ℂ] E) (L : List (E ≃ₗᵢ[ℂ] E)) :
    chronologicalEvolution (A :: L) = A.trans (chronologicalEvolution L) := by
  unfold chronologicalEvolution
  rw [List.foldl_cons, LinearIsometryEquiv.refl_trans]
  exact foldl_trans L A

omit [CompleteSpace E] in
private theorem evolution_snoc (L : List (E ≃ₗᵢ[ℂ] E)) (A : E ≃ₗᵢ[ℂ] E) :
    chronologicalEvolution (L ++ [A]) = (chronologicalEvolution L).trans A := by
  simp [chronologicalEvolution, List.foldl_append]

omit [CompleteSpace E] in
private theorem evolution_reverse_transpose (b : HilbertBasis ι ℂ E)
    (L : List (E ≃ₗᵢ[ℂ] E))
    (hs : ∀ U ∈ L, ∀ i j, inner ℂ (b i) (U (b j)) = inner ℂ (b j) (U (b i)))
    (i j : ι) :
    inner ℂ (b i) (chronologicalEvolution L (b j)) =
      inner ℂ (b j) (chronologicalEvolution L.reverse (b i)) := by
  induction L generalizing i j with
  | nil =>
    classical
    change inner ℂ (b i) (b j) = inner ℂ (b j) (b i)
    have hb := orthonormal_iff_ite.mp b.orthonormal
    rw [hb i j, hb j i]
    simp only [eq_comm (a := j) (b := i)]
  | cons A L ih =>
    rw [evolution_cons, List.reverse_cons, evolution_snoc]
    exact trans_transposes b (hs A (List.mem_cons_self ..))
      (ih fun U hU => hs U (List.mem_cons_of_mem A hU)) i j

omit [CompleteSpace E] in
private theorem sliceTime_rev (period : ℝ) (cycles n : ℕ) (r : Fin (n + 1)) :
    sliceTime period cycles n r.rev = (cycles : ℝ) * period - sliceTime period cycles n r := by
  have hsum : ((r.rev.val + r.val + 1 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) := by
    congr 1
    have hr := r.isLt
    simp only [Fin.rev]
    omega
  push_cast at hsum
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  unfold sliceTime
  push_cast
  rw [show (r.rev.val : ℝ) + 1 / 2 = (n + 1 : ℝ) - ((r.val : ℝ) + 1 / 2) by linarith]
  rw [sub_mul]
  congr 1
  field_simp

omit [CompleteSpace E] in
private theorem hamiltonian_rev {b : HilbertBasis ι ℂ E} (d : CyclicDrive (Ω := Ω) b)
    (n : ℕ) (r : Fin (n + 1)) :
    d.hamiltonian (sliceTime d.period d.cycles n r.rev) =
      d.hamiltonian (sliceTime d.period d.cycles n r) := by
  have hperiod (t : ℝ) (k : ℕ) :
      d.hamiltonian (t + (k : ℝ) * d.period) = d.hamiltonian t := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc, d.periodic, ih]
  rw [sliceTime_rev, sub_eq_neg_add, hperiod, d.reflection]

omit [CompleteSpace E] in
private theorem slices_reverse {b : HilbertBasis ι ℂ E} (d : CyclicDrive (Ω := Ω) b) (n : ℕ) :
    (List.ofFn (d.slices n)).reverse = List.ofFn (d.slices n) := by
  have hmirror (r : Fin (n + 1)) : d.slices n r.rev = d.slices n r := by
    have hr := d.slices_spec n r.rev
    rw [hamiltonian_rev d n r] at hr
    exact spectralStep_unique hr (d.slices_spec n r)
  apply List.ext_getElem
  · simp
  · intro i hi hj
    rw [List.getElem_reverse, List.getElem_ofFn, List.getElem_ofFn]
    let r : Fin (n + 1) := ⟨i, by simpa using hj⟩
    convert hmirror r using 2
    apply Fin.ext
    simp only [r, Fin.rev, List.length_ofFn]
    omega

omit [CompleteSpace E] in
private theorem adjoint_entry_of_symmetry (b : HilbertBasis ι ℂ E)
    (U : E ≃ₗᵢ[ℂ] E)
    (h : ∀ i j, inner ℂ (b i) (U (b j)) = inner ℂ (b j) (U (b i))) (i j : ι) :
    inner ℂ (b i) (U.symm (b j)) = star (inner ℂ (b i) (U (b j))) := by
  rw [← U.inner_map_map (b i) (U.symm (b j)), U.apply_symm_apply]
  rw [← inner_conj_symm (𝕜 := ℂ), h j i]
  rfl

theorem solution [Countable ι] [Nonempty ι]
    (b : HilbertBasis ι ℂ E) (d : CyclicDrive (Ω := Ω) b) :
    (∀ n i j,
      inner ℂ (b i) ((chronologicalEvolution (List.ofFn (d.slices n))).symm (b j)) =
        star (inner ℂ (b i) (chronologicalEvolution (List.ofFn (d.slices n)) (b j)))) ∧
    (∀ i j, inner ℂ (b i) (d.evolution.symm (b j)) =
      star (inner ℂ (b i) (d.evolution (b j)))) := by
  have hfinite (n : ℕ) (i j : ι) :
      inner ℂ (b i) (chronologicalEvolution (List.ofFn (d.slices n)) (b j)) =
        inner ℂ (b j) (chronologicalEvolution (List.ofFn (d.slices n)) (b i)) := by
    conv_rhs => rw [← slices_reverse d n]
    apply evolution_reverse_transpose
    intro U hU
    obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hU
    exact spectralStep_symmetric (d.slices_spec n r)
  refine ⟨fun n => adjoint_entry_of_symmetry b _ (hfinite n), ?_⟩
  apply adjoint_entry_of_symmetry b
  intro i j
  have hij := tendsto_const_nhds.inner (𝕜 := ℂ) (x := b i) (d.evolution_limit (b j))
  have hji := tendsto_const_nhds.inner (𝕜 := ℂ) (x := b j) (d.evolution_limit (b i))
  apply tendsto_nhds_unique hij
  refine hji.congr' (Eventually.of_forall fun n => ?_)
  exact (hfinite n i j).symm
