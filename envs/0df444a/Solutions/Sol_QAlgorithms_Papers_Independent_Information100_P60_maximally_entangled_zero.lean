-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P60.maximally_entangled_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T05:21:12.618228+00:00
-- url     : https://prove2.me/submissions/11853255-9fb6-4297-851c-6308b4715459

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60

-- ===== P60A

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder

namespace X4P60
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

variable {d : ℕ}

lemma kraus_psd {N : Superop (Fin d) (Fin d)} (hN : IsChannel N) {X : Mat (Fin d)}
    (hX : X.PosSemidef) : (N X).PosSemidef := by
  obtain ⟨m, E, -, hE⟩ := hN
  rw [hE, krausApply]
  exact Matrix.posSemidef_sum _ fun j _ => hX.mul_mul_conjTranspose_same (E j)

lemma kraus_trace {N : Superop (Fin d) (Fin d)} (hN : IsChannel N) (X : Mat (Fin d)) :
    (N X).trace = X.trace := by
  obtain ⟨m, E, hK, hE⟩ := hN
  rw [hE, krausApply, Matrix.trace_sum]
  have : ∀ j, (E j * X * (E j)ᴴ).trace = ((E j)ᴴ * E j * X).trace := fun j => by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp_rw [this, ← Matrix.trace_sum, ← Finset.sum_mul]
  rw [show (∑ j, (E j)ᴴ * E j) = 1 from hK, Matrix.one_mul]

lemma perm_unitary (σ : Equiv.Perm (Fin d)) :
    (σ.permMatrix ℂ) ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix,
    ← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]

lemma perm_conj_diag (σ : Equiv.Perm (Fin d)) (l : Fin d → ℂ) :
    σ.permMatrix ℂ * Matrix.diagonal l * (σ.permMatrix ℂ)ᴴ = Matrix.diagonal (l ∘ σ) := by
  rw [Matrix.conjTranspose_permMatrix, Equiv.Perm.permMatrix, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  simp [Matrix.diagonal_apply, Equiv.Perm.inv_def, σ.injective.eq_iff]


lemma single_psd (j : Fin d) : (Matrix.single j j (1 : ℂ)).PosSemidef := by
  rw [← Matrix.diagonal_single]
  refine Matrix.PosSemidef.diagonal fun i => ?_
  by_cases h : i = j
  · subst h; simp
  · simp [h]

lemma unital_sim (N : Maps d d) (hN : IsChannel (N : Superop (Fin d) (Fin d))) (hu : N 1 = 1)
    (ρ : Mat (Fin d)) (hρ : ρ.PosSemidef) :
    ∃ c : Equiv.Perm (Fin d) → ℝ, ∃ U : Equiv.Perm (Fin d) → Matrix.unitaryGroup (Fin d) ℂ,
      (∀ σ, 0 ≤ c σ) ∧ ∑ σ, c σ = 1 ∧
      N ρ = ∑ σ, (c σ : ℂ) • ((U σ : Mat (Fin d)) * ρ * (U σ : Mat (Fin d))ᴴ) := by
  have hH := hρ.1
  have hS := (kraus_psd hN hρ).1
  have hVm := hH.eigenvectorUnitary.2
  have hWm := hS.eigenvectorUnitary.2
  set V : Mat (Fin d) := (hH.eigenvectorUnitary : Mat (Fin d)) with hV
  set W : Mat (Fin d) := (hS.eigenvectorUnitary : Mat (Fin d)) with hW
  set l := hH.eigenvalues
  set μ := hS.eigenvalues
  have hVV : Vᴴ * V = 1 := Unitary.coe_star_mul_self _
  have hVV' : V * Vᴴ = 1 := Unitary.coe_mul_star_self _
  have hWW : Wᴴ * W = 1 := Unitary.coe_star_mul_self _
  have hWW' : W * Wᴴ = 1 := Unitary.coe_mul_star_self _
  have hρV : ρ = V * Matrix.diagonal (RCLike.ofReal ∘ l) * Vᴴ := by
    have := hH.spectral_theorem; rw [Unitary.conjStarAlgAut_apply] at this; exact this
  have hNW : Wᴴ * N ρ * W = Matrix.diagonal (RCLike.ofReal ∘ μ) := by
    have := hS.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at this; exact this
  set Mx : Fin d → Mat (Fin d) := fun j => Wᴴ * N (V * Matrix.single j j 1 * Vᴴ) * W with hMx
  have hMpsd : ∀ j, (Mx j).PosSemidef := fun j =>
    (kraus_psd hN ((single_psd j).mul_mul_conjTranspose_same V)).conjTranspose_mul_mul_same W
  have hsum : ∑ j, Mx j = 1 := by
    simp only [hMx, ← Finset.sum_mul, ← Finset.mul_sum, ← map_sum]
    rw [Matrix.sum_single_one, Matrix.mul_one, hVV', hu, Matrix.mul_one, hWW]
  have htr : ∀ j, (Mx j).trace = 1 := fun j => by
    simp only [hMx]
    rw [Matrix.trace_mul_cycle, hWW', Matrix.one_mul, kraus_trace hN, Matrix.trace_mul_cycle,
      hVV, Matrix.one_mul, Matrix.trace_single_eq_same]
  have hdec : Wᴴ * N ρ * W = ∑ j, ((l j : ℝ) : ℂ) • Mx j := by
    have : ρ = ∑ j, ((l j : ℝ) : ℂ) • (V * Matrix.single j j 1 * Vᴴ) := by
      rw [hρV, ← Matrix.sum_single_eq_diagonal]
      simp only [Matrix.mul_sum, Matrix.sum_mul, Function.comp_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hs : ∀ a : ℂ, Matrix.single j j a = a • Matrix.single j j (1:ℂ) := fun a => by
        rw [Matrix.smul_single, smul_eq_mul, mul_one]
      rw [hs, Matrix.mul_smul, Matrix.smul_mul]
      rfl
    rw [this, map_sum]
    simp only [map_smul, Matrix.mul_sum, Matrix.sum_mul, Matrix.smul_mul, Matrix.mul_smul, hMx]
  have hμ : ∀ i, μ i = ∑ j, l j * (Mx j i i).re := fun i => by
    have := congrArg (fun A => (A i i).re) (hNW.symm.trans hdec)
    simpa [Matrix.sum_apply] using this
  set D : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun i j => (Mx j i i).re with hD
  have hDs : D ∈ doublyStochastic ℝ (Fin d) := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨fun i j => ?_, fun i => ?_, fun j => ?_⟩
    · exact (Complex.nonneg_iff.mp ((hMpsd j).diag_nonneg)).1
    · have := congrArg (fun A => (A i i).re) hsum
      simpa [hD, Matrix.sum_apply] using this
    · have := congrArg Complex.re (htr j)
      simpa [hD, Matrix.trace] using this
  obtain ⟨c, hc0, hc1, hcD⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hDs
  have hμ' : ∀ i, μ i = ∑ σ, c σ * l (σ i) := fun i => by
    rw [hμ]
    have : ∀ j, (Mx j i i).re = D i j := fun j => rfl
    simp_rw [this, ← hcD, Matrix.sum_apply, Matrix.smul_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, mul_comm]
  have hUm : ∀ σ : Equiv.Perm (Fin d), W * σ.permMatrix ℂ * Vᴴ ∈ Matrix.unitaryGroup (Fin d) ℂ :=
    fun σ => Submonoid.mul_mem _ (Submonoid.mul_mem _ hWm (perm_unitary σ))
      (by rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mem hVm)
  refine ⟨c, fun σ => ⟨_, hUm σ⟩, hc0, hc1, ?_⟩
  have hNρ : N ρ = W * Matrix.diagonal (RCLike.ofReal ∘ μ) * Wᴴ := by
    rw [← hNW, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hWW', Matrix.one_mul, Matrix.mul_assoc,
      hWW', Matrix.mul_one]
  have hterm : ∀ σ : Equiv.Perm (Fin d),
      (W * σ.permMatrix ℂ * Vᴴ) * ρ * (W * σ.permMatrix ℂ * Vᴴ)ᴴ =
        W * Matrix.diagonal ((RCLike.ofReal ∘ l) ∘ σ) * Wᴴ := fun σ => by
    rw [← perm_conj_diag, hρV]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Vᴴ V, hVV, Matrix.one_mul, ← Matrix.mul_assoc Vᴴ V, hVV,
      Matrix.one_mul]
  have hdiag : Matrix.diagonal (RCLike.ofReal ∘ μ : Fin d → ℂ) =
      ∑ σ, ((c σ : ℝ) : ℂ) • Matrix.diagonal ((RCLike.ofReal ∘ l : Fin d → ℂ) ∘ σ) := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.diagonal_apply, Function.comp_apply]
    split_ifs with h
    · rw [hμ']
      push_cast
      simp [smul_eq_mul]
    · simp
  simp only [hterm]
  rw [hNρ, hdiag, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul]

end X4P60

end

-- ===== P60B

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder ENNReal
open Filter Topology

namespace X4P60
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

variable {d : ℕ}

/-- The mixed-unitary map as a continuous linear map. -/
def mixMap (c : Equiv.Perm (Fin d) → ℝ) (U : Equiv.Perm (Fin d) → Matrix.unitaryGroup (Fin d) ℂ) :
    Maps d d :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => ∑ σ, (c σ : ℂ) • ((U σ : Mat (Fin d)) * X * (U σ : Mat (Fin d))ᴴ)
      map_add' := fun X Y => by
        simp only [Matrix.mul_add, Matrix.add_mul, smul_add, Finset.sum_add_distrib]
      map_smul' := fun a X => by
        simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [smul_comm] }

lemma mixMap_apply (c : Equiv.Perm (Fin d) → ℝ)
    (U : Equiv.Perm (Fin d) → Matrix.unitaryGroup (Fin d) ℂ) (X : Mat (Fin d)) :
    mixMap c U X = ∑ σ, (c σ : ℂ) • ((U σ : Mat (Fin d)) * X * (U σ : Mat (Fin d))ᴴ) := rfl

lemma mixMap_mem (c : Equiv.Perm (Fin d) → ℝ)
    (U : Equiv.Perm (Fin d) → Matrix.unitaryGroup (Fin d) ℂ) (hc0 : ∀ σ, 0 ≤ c σ)
    (hc1 : ∑ σ, c σ = 1) : mixMap c U ∈ MU d := by
  set e := (Fintype.equivFin (Equiv.Perm (Fin d))).symm
  refine ⟨?_, Fintype.card (Equiv.Perm (Fin d)), c ∘ e, U ∘ e, fun j => hc0 _, ?_, fun X => ?_⟩
  · refine ⟨Fintype.card (Equiv.Perm (Fin d)),
      fun j => ((Real.sqrt (c (e j)) : ℝ) : ℂ) • (U (e j) : Mat (Fin d)), ?_, fun X => ?_⟩
    · rw [IsKrausFamily]
      simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      have : ∀ j, (U (e j) : Mat (Fin d))ᴴ * (U (e j) : Mat (Fin d)) = 1 := fun j =>
        Unitary.coe_star_mul_self _
      simp only [this, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (hc0 _)]
      rw [← Finset.sum_smul, Equiv.sum_comp e (fun σ => ((c σ : ℝ) : ℂ))]
      rw [← Complex.ofReal_sum, hc1]; simp
    · rw [mixMap_apply, krausApply, ← Equiv.sum_comp e]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hc0 _)]
  · simp only [Function.comp_apply]
    rw [Equiv.sum_comp e c, hc1]
  · rw [mixMap_apply, ← Equiv.sum_comp e]
    rfl

/-- embedding of `Fin d` into the registers for `r = k = 1`. -/
def fe (a : Fin d) : Reg 1 d 1 := (fun _ => 0, fun _ => a)
def ge (p : Reg 1 d 1) : Fin d := p.2 0

lemma ge_fe (a : Fin d) : ge (fe a) = a := rfl
lemma fe_ge (p : Reg 1 d 1) : fe (ge p) = p := by
  obtain ⟨p1, p2⟩ := p
  refine Prod.ext (Subsingleton.elim _ _) ?_
  funext i
  rw [Subsingleton.elim i 0]
  rfl

def eq1 : Fin d ≃ Reg 1 d 1 where
  toFun := fe
  invFun := ge
  left_inv := ge_fe
  right_inv := fe_ge

lemma output_eq (Φ : Maps d d) (X : Mat (Reg 1 d 1)) :
    output 1 1 Φ X = (Φ (X.submatrix fe fe)).submatrix ge ge := by
  ext p q
  rw [← fe_ge p, ← fe_ge q]
  simp only [output, idTensorSuperop, piSuperop, Matrix.of_apply, Matrix.submatrix_apply,
    Fin.prod_univ_one]
  conv_rhs => rw [Matrix.matrix_eq_sum_single (X.submatrix fe fe)]
  rw [map_sum, Matrix.sum_apply, ← (Equiv.funUnique (Fin 1) (Fin d)).symm.sum_comp]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum, Matrix.sum_apply, ← (Equiv.funUnique (Fin 1) (Fin d)).symm.sum_comp]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hs : Matrix.single a b (X.submatrix fe fe a b) = (X.submatrix fe fe a b) • Matrix.single a b 1 := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [hs, map_smul, Matrix.smul_apply, smul_eq_mul]
  rfl

lemma trace_ge (A : Mat (Fin d)) : (A.submatrix ge ge).trace = A.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact Fintype.sum_equiv eq1.symm _ _ (fun p => rfl)

lemma trace_fe (A : Mat (Reg 1 d 1)) : (A.submatrix fe fe).trace = A.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact Fintype.sum_equiv eq1 _ _ (fun p => rfl)

lemma trace_copies {I : Type*} [Fintype I] [DecidableEq I] (m : ℕ) (Y : Mat I) :
    (copies m Y).trace = Y.trace ^ m := by
  simp only [Matrix.trace, Matrix.diag, copies, Matrix.of_apply]
  rw [← Fin.prod_const, Finset.prod_univ_sum, Fintype.piFinset_univ]

end X4P60

end

-- ===== P60C

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder ENNReal
open Filter Topology

namespace X4P60
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

variable {d : ℕ}

lemma sim_output (N : Maps d d) (hN : IsChannel (N : Superop (Fin d) (Fin d))) (hu : N 1 = 1)
    (X : Mat (Reg 1 d 1)) (hX : X.PosSemidef) :
    ∃ Phi ∈ MU d, output 1 1 Phi X = output 1 1 N X := by
  obtain ⟨c, U, hc0, hc1, h⟩ := unital_sim N hN hu _ (hX.submatrix fe)
  refine ⟨mixMap c U, mixMap_mem c U hc0 hc1, ?_⟩
  rw [output_eq, output_eq, mixMap_apply, h]

lemma trace_output (N : Maps d d) (hN : IsChannel (N : Superop (Fin d) (Fin d)))
    (X : Mat (Reg 1 d 1)) : (output 1 1 N X).trace = X.trace := by
  rw [output_eq, trace_ge, kraus_trace hN, trace_fe]

lemma rate_bound (N : Maps d d) (hN : IsChannel (N : Superop (Fin d) (Fin d))) (hu : N 1 = 1)
    (m : ℕ) (eps : ℝ) (he1 : eps < 1) :
    blockRate 1 (MU d) N 1 (admissible 1 d 1 .unrestricted) m eps ≤
      ENNReal.ofReal (-Real.logb 2 (1 - eps)) / ((1 * (m + 1) : ℕ) : ℝ≥0∞) := by
  unfold blockRate
  refine ENNReal.div_le_div_right (iSup_le fun X => ?_) _
  obtain ⟨Phi, hPhi, hout⟩ := sim_output N hN hu X.1 X.2.1.1
  unfold testingBits
  refine iSup_le fun T => ?_
  have hmem : copies (m + 1) (output 1 1 N X.1) ∈
      {Y | ∃ Phi ∈ MU d, Y = copies (m + 1) (output 1 1 Phi X.1)} := ⟨Phi, hPhi, by rw [hout]⟩
  have h1 := T.2.2 _ hmem
  have htr : (copies (m + 1) (output 1 1 N X.1)).trace = 1 := by
    rw [trace_copies, trace_output N hN, X.2.1.2, one_pow]
  have hp : 1 - eps ≤ effectProb T.1 (copies (m + 1) (output 1 1 N X.1)) := by
    unfold effectProb at h1 ⊢
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re, htr] at h1
    simp only [Complex.one_re] at h1
    linarith
  rw [if_neg (by linarith)]
  apply ENNReal.ofReal_le_ofReal
  exact neg_le_neg (Real.logb_le_logb_of_le (by norm_num) (by linarith) hp)

lemma liminf_zero (N : Maps d d) (hN : IsChannel (N : Superop (Fin d) (Fin d))) (hu : N 1 = 1)
    (eps : ℝ) (he1 : eps < 1) :
    liminf (fun m => blockRate 1 (MU d) N 1 (admissible 1 d 1 .unrestricted) m eps) atTop = 0 := by
  refine le_antisymm ?_ (zero_le)
  set C := ENNReal.ofReal (-Real.logb 2 (1 - eps))
  have ht : Tendsto (fun m : ℕ => C / ((1 * (m + 1) : ℕ) : ℝ≥0∞)) atTop (𝓝 0) := by
    have h0 := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
    have h2 := ENNReal.Tendsto.const_mul h0 (Or.inr ENNReal.ofReal_ne_top) (a := C)
    rw [mul_zero] at h2
    refine h2.congr fun m => ?_
    simp [div_eq_mul_inv]
  calc _ ≤ liminf (fun m : ℕ => C / ((1 * (m + 1) : ℕ) : ℝ≥0∞)) atTop :=
        liminf_le_liminf (Eventually.of_forall fun m => rate_bound N hN hu m eps he1)
    _ = 0 := ht.liminf_eq

theorem main (N : Maps d d) (hN : IsChannel (N : Superop (Fin d) (Fin d))) (hu : N 1 = 1) :
    blockExponent 1 (MU d) N 1 .unrestricted = 0 := by
  unfold blockExponent operational
  have : NeBot (𝓝[Set.Ioo (0:ℝ) 1] 0) := left_nhdsWithin_Ioo_neBot one_pos
  rw [liminf_congr (eventually_nhdsWithin_of_forall fun eps he =>
    liminf_zero N hN hu eps he.2 : ∀ᶠ eps in 𝓝[Set.Ioo (0:ℝ) 1] 0, _ = (fun _ => (0:ℝ≥0∞)) eps)]
  exact liminf_const 0

end X4P60

end

-- ===== P60D

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder ENNReal
open Filter Topology

namespace X4P60
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

variable {d : ℕ}

/-- mixed-unitary map over an arbitrary finite index. -/
def mixI {ι : Type} [Fintype ι] (c : ι → ℝ) (U : ι → Matrix.unitaryGroup (Fin d) ℂ) : Maps d d :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => ∑ σ, (c σ : ℂ) • ((U σ : Mat (Fin d)) * X * (U σ : Mat (Fin d))ᴴ)
      map_add' := fun X Y => by
        simp only [Matrix.mul_add, Matrix.add_mul, smul_add, Finset.sum_add_distrib]
      map_smul' := fun a X => by
        simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [smul_comm] }

lemma mixI_apply {ι : Type} [Fintype ι] (c : ι → ℝ) (U : ι → Matrix.unitaryGroup (Fin d) ℂ)
    (X : Mat (Fin d)) :
    mixI c U X = ∑ σ, (c σ : ℂ) • ((U σ : Mat (Fin d)) * X * (U σ : Mat (Fin d))ᴴ) := rfl

lemma mixI_mem {ι : Type} [Fintype ι] (c : ι → ℝ) (U : ι → Matrix.unitaryGroup (Fin d) ℂ)
    (hc0 : ∀ σ, 0 ≤ c σ) (hc1 : ∑ σ, c σ = 1) : mixI c U ∈ MU d := by
  set e := (Fintype.equivFin ι).symm
  refine ⟨?_, Fintype.card ι, c ∘ e, U ∘ e, fun j => hc0 _, ?_, fun X => ?_⟩
  · refine ⟨Fintype.card ι,
      fun j => ((Real.sqrt (c (e j)) : ℝ) : ℂ) • (U (e j) : Mat (Fin d)), ?_, fun X => ?_⟩
    · rw [IsKrausFamily]
      simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      have : ∀ j, (U (e j) : Mat (Fin d))ᴴ * (U (e j) : Mat (Fin d)) = 1 := fun j =>
        Unitary.coe_star_mul_self _
      simp only [this, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (hc0 _)]
      rw [← Finset.sum_smul, Equiv.sum_comp e (fun σ => ((c σ : ℝ) : ℂ))]
      rw [← Complex.ofReal_sum, hc1]; simp
    · rw [mixI_apply, krausApply, ← Equiv.sum_comp e]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hc0 _)]
  · simp only [Function.comp_apply]
    rw [Equiv.sum_comp e c, hc1]
  · rw [mixI_apply, ← Equiv.sum_comp e]
    rfl

/-! Depolarizing channel on qutrits as a unitary mixture. -/

def sgn (b : Bool) : ℂ := if b then -1 else 1

def signD (b : Bool × Bool × Bool) : Mat (Fin 3) :=
  Matrix.diagonal ![sgn b.1, sgn b.2.1, sgn b.2.2]

def rotP (a : Fin 3) : Mat (Fin 3) := ((finRotate 3) ^ (a : ℕ)).permMatrix ℂ

lemma signD_mem (b : Bool × Bool × Bool) : signD b ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, signD,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> cases b.1 <;> cases b.2.1 <;> cases b.2.2 <;> simp [sgn]

lemma sign_twirl (M : Mat (Fin 3)) :
    ∑ b, signD b * M * (signD b)ᴴ = (8 : ℂ) • Matrix.diagonal (fun i => M i i) := by
  ext i j
  simp only [Matrix.sum_apply, signD, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul,
    Matrix.mul_diagonal, Matrix.smul_apply, Matrix.diagonal_apply, Fintype.sum_prod_type,
    Fintype.sum_bool]
  fin_cases i <;> fin_cases j <;> simp [sgn] <;> ring

lemma rot_sum (m : Fin 3 → ℂ) (i : Fin 3) : ∑ a : Fin 3, m (((finRotate 3) ^ (a : ℕ)) i) = ∑ j, m j := by
  have h1 : (finRotate 3) 0 = 1 := rfl
  have h2 : (finRotate 3) 1 = 2 := rfl
  have h3 : (finRotate 3) 2 = 0 := rfl
  fin_cases i <;> simp [Fin.sum_univ_three, pow_succ, Equiv.Perm.mul_apply, h1, h2, h3] <;> ring

lemma depol (M : Mat (Fin 3)) :
    ∑ p : Fin 3 × (Bool × Bool × Bool),
      (rotP p.1 * signD p.2) * M * (rotP p.1 * signD p.2)ᴴ = (8 * M.trace) • (1 : Mat (Fin 3)) := by
  rw [Fintype.sum_prod_type]
  have : ∀ a : Fin 3, ∑ b, (rotP a * signD b) * M * (rotP a * signD b)ᴴ =
      (8 : ℂ) • Matrix.diagonal ((fun i => M i i) ∘ ((finRotate 3 ^ (a : ℕ)))) := by
    intro a
    have : ∀ b, (rotP a * signD b) * M * (rotP a * signD b)ᴴ =
        rotP a * (signD b * M * (signD b)ᴴ) * (rotP a)ᴴ := fun b => by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    simp only [this]
    rw [← Finset.sum_mul, ← Finset.mul_sum, sign_twirl, Matrix.mul_smul, Matrix.smul_mul, rotP,
      perm_conj_diag]
  simp only [this]
  rw [← Finset.smul_sum]
  ext i j
  simp only [Matrix.smul_apply, Matrix.sum_apply, Matrix.diagonal_apply, Function.comp_apply,
    Matrix.one_apply, smul_eq_mul]
  split_ifs with h
  · subst h; rw [rot_sum (fun i => M i i) i, Matrix.trace]; simp
  · simp

end X4P60

end

-- ===== P60E

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder ENNReal
open Filter Topology

namespace X4P60

def dl (i j : Fin 3) : ℂ := if i = j then 1 else 0

variable (m : Fin 3 → Fin 3 → ℂ)
  (hm1 : ∀ j j', ∑ i, m i j * conj (m i j') = if j = j' then 1/3 else 0)
  (hm2 : ∀ i i', ∑ j, m i j * conj (m i' j) = if i = i' then 1/3 else 0)

include hm1 in
lemma sum_TT (k k' l l' : Fin 3) :
    ∑ i, ∑ j, ∑ i', ∑ j', m i j * conj (m i' j') *
      ((dl i i' * dl k k') * (dl j j' * dl l l')) = dl k k' * dl l l' := by
  have : ∀ i j i' j', m i j * conj (m i' j') * ((dl i i' * dl k k') * (dl j j' * dl l l')) =
      dl k k' * dl l l' * (dl i i' * (dl j j' * (m i j * conj (m i' j')))) := fun _ _ _ _ => by ring
  simp_rw [this, ← Finset.mul_sum]
  simp only [dl, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  simp only [hm1, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  norm_num

include hm1 in
lemma sum_TR (P Q : Fin 3 → Fin 3 → ℂ) (k k' l l' : Fin 3) :
    ∑ i, ∑ j, ∑ i', ∑ j', m i j * conj (m i' j') *
      ((dl i i' * dl k k') * (P l j * conj (Q l' j'))) =
      dl k k' * (1/3 * ∑ j, P l j * conj (Q l' j)) := by
  have : ∀ i j i' j', m i j * conj (m i' j') * ((dl i i' * dl k k') * (P l j * conj (Q l' j'))) =
      dl k k' * (dl i i' * (m i j * conj (m i' j') * (P l j * conj (Q l' j')))) :=
    fun _ _ _ _ => by ring
  simp_rw [this, ← Finset.mul_sum]
  simp only [dl, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  congr 1
  rw [Finset.sum_comm]
  have h2 : ∀ j j', ∑ i, m i j * conj (m i j') * (P l j * conj (Q l' j')) =
      (if j = j' then 1/3 else 0) * (P l j * conj (Q l' j')) := fun j j' => by
    rw [← Finset.sum_mul, hm1]
  simp_rw [Finset.sum_comm (γ := Fin 3) (s := Finset.univ) (t := Finset.univ)
    (f := fun i j' => m i _ * conj (m i j') * _)]
  simp only [h2, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.mul_sum]

include hm2 in
lemma sum_RT (P Q : Fin 3 → Fin 3 → ℂ) (k k' l l' : Fin 3) :
    ∑ i, ∑ j, ∑ i', ∑ j', m i j * conj (m i' j') *
      ((P k i * conj (Q k' i')) * (dl j j' * dl l l')) =
      dl l l' * (1/3 * ∑ i, P k i * conj (Q k' i)) := by
  have : ∀ i j i' j', m i j * conj (m i' j') * ((P k i * conj (Q k' i')) * (dl j j' * dl l l')) =
      dl l l' * (dl j j' * (m i j * conj (m i' j') * (P k i * conj (Q k' i')))) :=
    fun _ _ _ _ => by ring
  simp_rw [this, ← Finset.mul_sum]
  simp only [dl, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  congr 1
  have h2 : ∀ i i', ∑ j, m i j * conj (m i' j) * (P k i * conj (Q k' i')) =
      (if i = i' then 1/3 else 0) * (P k i * conj (Q k' i')) := fun i i' => by
    rw [← Finset.sum_mul, hm2]
  simp_rw [Finset.sum_comm (γ := Fin 3) (s := Finset.univ) (t := Finset.univ)
    (f := fun j i' => m _ j * conj (m i' j) * _)]
  simp only [h2, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.mul_sum]

lemma sum_RR (P Q P' Q' : Fin 3 → Fin 3 → ℂ) (k k' l l' : Fin 3) :
    ∑ i, ∑ j, ∑ i', ∑ j', m i j * conj (m i' j') *
      ((P k i * conj (Q k' i')) * (P' l j * conj (Q' l' j'))) =
      (∑ i, ∑ j, P k i * P' l j * m i j) * conj (∑ i, ∑ j, Q k' i * Q' l' j * m i j) := by
  simp only [map_sum, map_mul]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j' _ => ?_
  ring

include hm1 in
lemma sum_TS (C : Fin 3 → Fin 3 → ℂ) (k k' l l' : Fin 3) :
    ∑ i, ∑ j, ∑ i', ∑ j', m i j * conj (m i' j') *
      ((dl i i' * dl k k') * (C l j' * conj (C l' j))) =
      dl k k' * (1/3 * ∑ j, C l j * conj (C l' j)) := by
  have : ∀ i j i' j', m i j * conj (m i' j') * ((dl i i' * dl k k') * (C l j' * conj (C l' j))) =
      dl k k' * (dl i i' * (m i j * conj (m i' j') * (C l j' * conj (C l' j)))) :=
    fun _ _ _ _ => by ring
  simp_rw [this, ← Finset.mul_sum]
  simp only [dl, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  congr 1
  rw [Finset.sum_comm]
  have h2 : ∀ j j', ∑ i, m i j * conj (m i j') * (C l j' * conj (C l' j)) =
      (if j = j' then 1/3 else 0) * (C l j' * conj (C l' j)) := fun j j' => by
    rw [← Finset.sum_mul, hm1]
  simp_rw [Finset.sum_comm (γ := Fin 3) (s := Finset.univ) (t := Finset.univ)
    (f := fun i j' => m i _ * conj (m i j') * _)]
  simp only [h2, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.mul_sum]

include hm2 in
lemma sum_ST (C : Fin 3 → Fin 3 → ℂ) (k k' l l' : Fin 3) :
    ∑ i, ∑ j, ∑ i', ∑ j', m i j * conj (m i' j') *
      ((C k i' * conj (C k' i)) * (dl j j' * dl l l')) =
      dl l l' * (1/3 * ∑ i, C k i * conj (C k' i)) := by
  have : ∀ i j i' j', m i j * conj (m i' j') * ((C k i' * conj (C k' i)) * (dl j j' * dl l l')) =
      dl l l' * (dl j j' * (m i j * conj (m i' j') * (C k i' * conj (C k' i)))) :=
    fun _ _ _ _ => by ring
  simp_rw [this, ← Finset.mul_sum]
  simp only [dl, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  congr 1
  have h2 : ∀ i i', ∑ j, m i j * conj (m i' j) * (C k i' * conj (C k' i)) =
      (if i = i' then 1/3 else 0) * (C k i' * conj (C k' i)) := fun i i' => by
    rw [← Finset.sum_mul, hm2]
  simp_rw [Finset.sum_comm (γ := Fin 3) (s := Finset.univ) (t := Finset.univ)
    (f := fun j i' => m _ j * conj (m i' j) * _)]
  simp only [h2, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.mul_sum]

lemma sum_SS (C : Fin 3 → Fin 3 → ℂ) (k k' l l' : Fin 3) :
    ∑ i, ∑ j, ∑ i', ∑ j', m i j * conj (m i' j') *
      ((C k i' * conj (C k' i)) * (C l j' * conj (C l' j))) =
      (∑ i, ∑ j, C k i * C l j * conj (m i j)) * conj (∑ i, ∑ j, C k' i * C l' j * conj (m i j)) := by
  rw [mul_comm]
  simp only [map_sum, map_mul, Complex.conj_conj]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j' _ => ?_
  ring

omit m in
lemma sum4_lin (F A B Cc D : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℂ) (a b c e : ℂ)
    (h : ∀ i j i' j', F i j i' j' = a * A i j i' j' + b * B i j i' j' + c * Cc i j i' j' +
      e * D i j i' j') :
    ∑ i, ∑ j, ∑ i', ∑ j', F i j i' j' = a * (∑ i, ∑ j, ∑ i', ∑ j', A i j i' j') +
      b * (∑ i, ∑ j, ∑ i', ∑ j', B i j i' j') + c * (∑ i, ∑ j, ∑ i', ∑ j', Cc i j i' j') +
      e * (∑ i, ∑ j, ∑ i', ∑ j', D i j i' j') := by
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum]

def fN (C : Fin 3 → Fin 3 → ℂ) (a b k k' : Fin 3) : ℂ :=
  1/2 * (dl a b * dl k k') - 1/2 * (C k b * conj (C k' a))

def fP (G : Fin 3 → Fin 3 → ℂ) (a b k k' : Fin 3) : ℂ :=
  1/6 * (dl a b * dl k k') + 1/2 * (G k a * conj (G k' b))

include hm1 hm2 in
lemma key (C G : Fin 3 → Fin 3 → ℂ) (hC : ∀ l l', ∑ j, C l j * conj (C l' j) = dl l l')
    (hG : ∀ l l', ∑ j, G l j * conj (G l' j) = dl l l')
    (hGC : ∀ k l, ∑ i, ∑ j, G k i * G l j * m i j = ∑ i, ∑ j, C k i * C l j * conj (m i j))
    (k k' l l' : Fin 3) :
    ∑ i, ∑ j, ∑ i', ∑ j', m i j * conj (m i' j') * (fN C i i' k k' * fN C j j' l l') =
    ∑ i, ∑ j, ∑ i', ∑ j', m i j * conj (m i' j') * (fP G i i' k k' * fP G j j' l l') := by
  rw [sum4_lin _
    (fun i j i' j' => m i j * conj (m i' j') * ((dl i i' * dl k k') * (dl j j' * dl l l')))
    (fun i j i' j' => m i j * conj (m i' j') * ((dl i i' * dl k k') * (C l j' * conj (C l' j))))
    (fun i j i' j' => m i j * conj (m i' j') * ((C k i' * conj (C k' i)) * (dl j j' * dl l l')))
    (fun i j i' j' => m i j * conj (m i' j') * ((C k i' * conj (C k' i)) * (C l j' * conj (C l' j))))
    (1/4) (-1/4) (-1/4) (1/4) (fun i j i' j' => by simp only [fN]; ring)]
  rw [sum4_lin (fun i j i' j' => m i j * conj (m i' j') * (fP G i i' k k' * fP G j j' l l'))
    (fun i j i' j' => m i j * conj (m i' j') * ((dl i i' * dl k k') * (dl j j' * dl l l')))
    (fun i j i' j' => m i j * conj (m i' j') * ((dl i i' * dl k k') * (G l j * conj (G l' j'))))
    (fun i j i' j' => m i j * conj (m i' j') * ((G k i * conj (G k' i')) * (dl j j' * dl l l')))
    (fun i j i' j' => m i j * conj (m i' j') * ((G k i * conj (G k' i')) * (G l j * conj (G l' j'))))
    (1/36) (1/12) (1/12) (1/4) (fun i j i' j' => by simp only [fP]; ring)]
  rw [sum_TT m hm1, sum_TS m hm1, sum_ST m hm2, sum_SS m, sum_TR m hm1,
    sum_RT m hm2, sum_RR m, hC, hC, hG, hG, hGC, hGC]
  ring

end X4P60

end

-- ===== P60F

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder ENNReal
open Filter Topology

namespace X4P60
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

variable {d : ℕ}

lemma trace_outk {k : ℕ} (f : Maps d d)
    (hf : ∀ a b, (f (Matrix.single a b 1)).trace = if a = b then 1 else 0) (X : Mat (Reg 1 d k)) :
    (output 1 k f X).trace = X.trace := by
  simp only [Matrix.trace, Matrix.diag, output, idTensorSuperop, piSuperop, Matrix.of_apply]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type,
    Fintype.sum_subsingleton _ (default : Fin k → Fin 1),
    Fintype.sum_subsingleton _ (default : Fin k → Fin 1)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  have : ∀ x' : Fin k → Fin d, ∑ p2 : Fin k → Fin d,
      X (default, x) (default, x') * ∏ i, f (Matrix.single (x i) (x' i) 1) (p2 i) (p2 i) =
      X (default, x) (default, x') * (if x = x' then 1 else 0) := fun x' => by
    rw [← Finset.mul_sum]
    congr 1
    have hp := Finset.prod_univ_sum (fun _ : Fin k => (Finset.univ : Finset (Fin d)))
      (fun i j => (f (Matrix.single (x i) (x' i) 1)) j j)
    rw [Fintype.piFinset_univ] at hp
    refine hp.symm.trans ?_
    simp only [Matrix.trace, Matrix.diag] at hf
    simp only [hf]
    by_cases h : x = x'
    · subst h; simp
    · obtain ⟨i, hi⟩ : ∃ i, x i ≠ x' i := by
        by_contra hc; exact h (funext fun i => by by_contra hi; exact hc ⟨i, hi⟩)
      rw [if_neg h]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- the MES probe matrix from a unitary `V`. -/
def probe (V : Mat (Fin 3)) : Mat (Reg 1 3 2) := Matrix.of (fun x y =>
    ((Real.sqrt 3 : ℂ)⁻¹ * V (x.2 1) (x.2 0)) * conj ((Real.sqrt 3 : ℂ)⁻¹ * V (y.2 1) (y.2 0)))

def mm (V : Mat (Fin 3)) (i j : Fin 3) : ℂ := (Real.sqrt 3 : ℂ)⁻¹ * V j i

lemma out_eq2 (f : Maps 3 3) (V : Mat (Fin 3)) (p q : Reg 1 3 2) :
    output 1 2 f (probe V) p q = ∑ i, ∑ j, ∑ i', ∑ j', mm V i j * conj (mm V i' j') *
      (f (Matrix.single i i' 1) (p.2 0) (q.2 0) * f (Matrix.single j j' 1) (p.2 1) (q.2 1)) := by
  simp only [output, idTensorSuperop, piSuperop, Matrix.of_apply, probe, Fin.prod_univ_two]
  rw [← (piFinTwoEquiv fun _ => Fin 3).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← (piFinTwoEquiv fun _ => Fin 3).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j' _ => ?_
  simp [mm, piFinTwoEquiv_symm_apply]

end X4P60

end

-- ===== P60G

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder ENNReal
open Filter Topology

namespace X4P60
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

lemma conj_entry (C : Mat (Fin 3)) (a b k k' : Fin 3) :
    (C * Matrix.single b a (1:ℂ) * Cᴴ : Mat (Fin 3)) k k' = C k b * conj (C k' a) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · rw [Matrix.mul_single_apply_same, mul_one, Matrix.conjTranspose_apply]; rfl
  · intro x _ hx; rw [Matrix.mul_single_apply_of_ne (hbj := hx), zero_mul]
  · simp

lemma N_entry (N : Maps 3 3) (U V : Matrix.unitaryGroup (Fin 3) ℂ)
    (h : ∀ X, N X = (V : Mat (Fin 3)) * wernerHolevo 3 ((U : Mat (Fin 3)) * X * (U : Mat (Fin 3))ᴴ) *
      (V : Mat (Fin 3))ᴴ) (a b k k' : Fin 3) :
    N (Matrix.single a b 1) k k' = fN ((V : Mat (Fin 3)) * ((U : Mat (Fin 3))ᴴ)ᵀ) a b k k' := by
  have hU : (U : Mat (Fin 3))ᴴ * U = 1 := Unitary.coe_star_mul_self _
  have hV : (V : Mat (Fin 3)) * (V : Mat (Fin 3))ᴴ = 1 := Unitary.coe_mul_star_self _
  have htr : ((U : Mat (Fin 3)) * Matrix.single a b 1 * (U : Mat (Fin 3))ᴴ).trace = dl a b := by
    rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul, dl]
    by_cases hab : a = b
    · subst hab; simp
    · rw [if_neg hab, Matrix.trace_single_eq_of_ne _ _ _ hab]
  have hT : ((U : Mat (Fin 3)) * Matrix.single a b 1 * (U : Mat (Fin 3))ᴴ)ᵀ =
      ((U : Mat (Fin 3))ᴴ)ᵀ * Matrix.single b a 1 * ((((U : Mat (Fin 3))ᴴ)ᵀ)ᴴ) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_single, Matrix.mul_assoc]
    congr 2
    ext i j; simp
  rw [h, wernerHolevo, htr, hT]
  set Cu := ((U : Mat (Fin 3))ᴴ)ᵀ
  have hM : (V : Mat (Fin 3)) * ((((3 : ℕ) : ℂ) - 1)⁻¹ • (dl a b • (1 : Mat (Fin 3)) -
      Cu * Matrix.single b a 1 * Cuᴴ)) * (V : Mat (Fin 3))ᴴ =
      (1/2 : ℂ) • (dl a b • (1 : Mat (Fin 3)) - ((V : Mat (Fin 3)) * Cu) * Matrix.single b a 1 *
        ((V : Mat (Fin 3)) * Cu)ᴴ) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, hV, Matrix.conjTranspose_mul]
    norm_num
    simp only [Matrix.mul_assoc]
  rw [hM, Matrix.smul_apply, Matrix.sub_apply, Matrix.smul_apply, conj_entry, Matrix.one_apply]
  unfold fN
  simp only [dl, smul_eq_mul]
  split_ifs <;> ring

end X4P60

end

-- ===== P60H

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder ENNReal
open Filter Topology

namespace X4P60
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

abbrev Idx := Option (Fin 3 × (Bool × Bool × Bool))

lemma tconj_mem (A : Mat (Fin 3)) (hA : A ∈ Matrix.unitaryGroup (Fin 3) ℂ) :
    (Aᴴ)ᵀ ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hA ⊢
  rw [Matrix.star_eq_conjTranspose] at hA ⊢
  have : ((Aᴴ)ᵀ)ᴴ = Aᵀ := by ext i j; simp
  rw [this, ← Matrix.transpose_mul, hA, Matrix.transpose_one]

def cw : Idx → ℝ
  | none => 1/2
  | some _ => 1/48

def Uw (G : Matrix.unitaryGroup (Fin 3) ℂ) : Idx → Matrix.unitaryGroup (Fin 3) ℂ
  | none => G
  | some p => ⟨rotP p.1 * signD p.2, Submonoid.mul_mem _ (perm_unitary _) (signD_mem _)⟩

lemma cw_sum : ∑ o, cw o = 1 := by
  rw [Fintype.sum_option]
  simp [cw]
  norm_num

lemma Phi_mem (G : Matrix.unitaryGroup (Fin 3) ℂ) : mixI cw (Uw G) ∈ MU 3 :=
  mixI_mem cw (Uw G) (fun o => by cases o <;> simp [cw]) cw_sum

lemma Phi_entry (G : Matrix.unitaryGroup (Fin 3) ℂ) (a b k k' : Fin 3) :
    mixI cw (Uw G) (Matrix.single a b 1) k k' = fP (G : Mat (Fin 3)) a b k k' := by
  rw [mixI_apply, Fintype.sum_option]
  simp only [cw, Uw]
  rw [← Finset.smul_sum]
  have hd := depol (Matrix.single a b 1)
  rw [hd,  Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.smul_apply,
    conj_entry, Matrix.one_apply]
  unfold fP dl
  by_cases hab : a = b
  · subst hab; rw [Matrix.trace_single_eq_same]; simp only [smul_eq_mul, if_true]
    split_ifs <;> push_cast <;> ring
  · rw [Matrix.trace_single_eq_of_ne _ _ _ hab]; simp only [smul_eq_mul, if_neg hab]
    split_ifs <;> push_cast <;> ring

end X4P60

end

-- ===== P60I

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder ENNReal
open Filter Topology

namespace X4P60
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

lemma s3 : (Real.sqrt 3 : ℂ)⁻¹ * conj ((Real.sqrt 3 : ℂ)⁻¹) = 1/3 := by
  rw [map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by norm_num)]
  norm_num

lemma unit_rows (A : Mat (Fin 3)) (hA : A ∈ Matrix.unitaryGroup (Fin 3) ℂ) (l l' : Fin 3) :
    ∑ j, A l j * conj (A l' j) = dl l l' := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hA
  have := congrFun (congrFun hA l) l'
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  simpa [dl] using this

lemma unit_cols (A : Mat (Fin 3)) (hA : A ∈ Matrix.unitaryGroup (Fin 3) ℂ) (i i' : Fin 3) :
    ∑ j, conj (A j i) * A j i' = dl i i' := by
  rw [Matrix.mem_unitaryGroup_iff'] at hA
  rw [Matrix.star_eq_conjTranspose] at hA
  have := congrFun (congrFun hA i) i'
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  simpa [dl] using this

lemma mm_hm1 (V : Mat (Fin 3)) (hV : V ∈ Matrix.unitaryGroup (Fin 3) ℂ) (j j' : Fin 3) :
    ∑ i, mm V i j * conj (mm V i j') = if j = j' then 1/3 else 0 := by
  have : ∀ i, mm V i j * conj (mm V i j') =
      ((Real.sqrt 3 : ℂ)⁻¹ * conj ((Real.sqrt 3 : ℂ)⁻¹)) * (V j i * conj (V j' i)) := fun i => by
    simp only [mm, map_mul]; ring
  simp_rw [this, ← Finset.mul_sum, unit_rows V hV, s3, dl]
  split_ifs <;> ring

lemma mm_hm2 (V : Mat (Fin 3)) (hV : V ∈ Matrix.unitaryGroup (Fin 3) ℂ) (i i' : Fin 3) :
    ∑ j, mm V i j * conj (mm V i' j) = if i = i' then 1/3 else 0 := by
  have : ∀ j, mm V i j * conj (mm V i' j) =
      ((Real.sqrt 3 : ℂ)⁻¹ * conj ((Real.sqrt 3 : ℂ)⁻¹)) * (conj (V j i') * V j i) := fun j => by
    simp only [mm, map_mul]; ring
  simp_rw [this, ← Finset.mul_sum, unit_cols V hV, s3, dl]
  by_cases h : i = i'
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h]; ring

lemma hGC_mat (C V : Mat (Fin 3)) (hV : V ∈ Matrix.unitaryGroup (Fin 3) ℂ) :
    (C * (Vᴴ)ᵀ) * Matrix.of (mm V) * (C * (Vᴴ)ᵀ)ᵀ = C * Matrix.of (fun i j => conj (mm V i j)) * Cᵀ := by
  have h1 : Matrix.of (mm V) = (Real.sqrt 3 : ℂ)⁻¹ • Vᵀ := by ext i j; simp [mm]
  have h2 : Matrix.of (fun i j => conj (mm V i j)) = (Real.sqrt 3 : ℂ)⁻¹ • Vᴴ := by
    ext i j; simp [mm, map_inv₀, Complex.conj_ofReal]
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hV
  have h3 : (Vᴴ)ᵀ * Vᵀ = 1 := by rw [← Matrix.transpose_mul, hV, Matrix.transpose_one]
  rw [h1, h2, Matrix.transpose_mul, Matrix.transpose_transpose]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Vᴴ)ᵀ Vᵀ, h3, Matrix.one_mul]

lemma ent (G M : Mat (Fin 3)) (k l : Fin 3) :
    (G * M * Gᵀ) k l = ∑ i, ∑ j, G k i * G l j * M i j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma hGC (C V : Mat (Fin 3)) (hV : V ∈ Matrix.unitaryGroup (Fin 3) ℂ) (k l : Fin 3) :
    ∑ i, ∑ j, (C * (Vᴴ)ᵀ) k i * (C * (Vᴴ)ᵀ) l j * mm V i j =
      ∑ i, ∑ j, C k i * C l j * conj (mm V i j) := by
  have := congrFun (congrFun (hGC_mat C V hV) k) l
  rw [ent, ent] at this
  simpa using this

end X4P60

end

-- ===== P60J

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder ENNReal
open Filter Topology

namespace X4P60
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

lemma out_match (N : Maps 3 3) (Ui Vo : Matrix.unitaryGroup (Fin 3) ℂ)
    (h : ∀ X, N X = (Vo : Mat (Fin 3)) * wernerHolevo 3 ((Ui : Mat (Fin 3)) * X * (Ui : Mat (Fin 3))ᴴ) *
      (Vo : Mat (Fin 3))ᴴ) (Vp : Matrix.unitaryGroup (Fin 3) ℂ) :
    ∃ Phi ∈ MU 3, output 1 2 Phi (probe Vp) = output 1 2 N (probe Vp) := by
  set C : Mat (Fin 3) := (Vo : Mat (Fin 3)) * ((Ui : Mat (Fin 3))ᴴ)ᵀ
  have hCm : C ∈ Matrix.unitaryGroup (Fin 3) ℂ := Submonoid.mul_mem _ Vo.2 (tconj_mem _ Ui.2)
  set Gm : Mat (Fin 3) := C * ((Vp : Mat (Fin 3))ᴴ)ᵀ
  have hGm : Gm ∈ Matrix.unitaryGroup (Fin 3) ℂ := Submonoid.mul_mem _ hCm (tconj_mem _ Vp.2)
  refine ⟨mixI cw (Uw ⟨Gm, hGm⟩), Phi_mem _, ?_⟩
  ext p q
  rw [out_eq2, out_eq2]
  simp_rw [Phi_entry, N_entry N Ui Vo h]
  exact (key (mm Vp) (mm_hm1 Vp Vp.2) (mm_hm2 Vp Vp.2) C Gm (unit_rows C hCm) (unit_rows Gm hGm)
    (hGC C Vp Vp.2) _ _ _ _).symm

lemma trace_probe (Vp : Matrix.unitaryGroup (Fin 3) ℂ) : (probe Vp).trace = 1 := by
  simp only [Matrix.trace, Matrix.diag, probe, Matrix.of_apply]
  rw [Fintype.sum_prod_type, Fintype.sum_subsingleton _ (default : Fin 2 → Fin 1)]
  rw [← (piFinTwoEquiv fun _ => Fin 3).symm.sum_comp, Fintype.sum_prod_type]
  have := fun j => mm_hm1 Vp Vp.2 j j
  simp only [if_true] at this
  simp only [piFinTwoEquiv_symm_apply, Fin.cons_one, Fin.cons_zero]
  simp only [mm] at this
  rw [Finset.sum_comm]
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  norm_num

lemma mes_eq (X : Mat (Reg 1 3 2)) (hX : X ∈ MESProbe 3) : ∃ Vp : Matrix.unitaryGroup (Fin 3) ℂ, X = probe Vp := by
  obtain ⟨Vp, rfl⟩ := hX
  exact ⟨Vp, by simp [probe]⟩

lemma rate_bound2 (N : Maps 3 3) (hN : IsChannel (N : Superop (Fin 3) (Fin 3)))
    (Ui Vo : Matrix.unitaryGroup (Fin 3) ℂ)
    (h : ∀ X, N X = (Vo : Mat (Fin 3)) * wernerHolevo 3 ((Ui : Mat (Fin 3)) * X * (Ui : Mat (Fin 3))ᴴ) *
      (Vo : Mat (Fin 3))ᴴ) (m : ℕ) (eps : ℝ) (he1 : eps < 1) :
    blockRate 1 (MU 3) N 2 (MESProbe 3) m eps ≤
      ENNReal.ofReal (-Real.logb 2 (1 - eps)) / ((2 * (m + 1) : ℕ) : ℝ≥0∞) := by
  unfold blockRate
  refine ENNReal.div_le_div_right (iSup_le fun X => ?_) _
  obtain ⟨Vp, hVp⟩ := mes_eq X.1 X.2
  obtain ⟨Phi, hPhi, hout⟩ := out_match N Ui Vo h Vp
  unfold testingBits
  refine iSup_le fun T => ?_
  have hmem : copies (m + 1) (output 1 2 N X.1) ∈
      {Y | ∃ Phi ∈ MU 3, Y = copies (m + 1) (output 1 2 Phi X.1)} :=
    ⟨Phi, hPhi, by rw [hVp, hout]⟩
  have h1 := T.2.2 _ hmem
  have hf : ∀ a b : Fin 3, ((N : Superop (Fin 3) (Fin 3)) (Matrix.single a b 1)).trace =
      if a = b then 1 else 0 := fun a b => by
    rw [kraus_trace hN]
    by_cases hab : a = b
    · subst hab; simp
    · rw [if_neg hab, Matrix.trace_single_eq_of_ne _ _ _ hab]
  have htr : (copies (m + 1) (output 1 2 N X.1)).trace = 1 := by
    rw [trace_copies, trace_outk N hf, hVp, trace_probe, one_pow]
  have hp : 1 - eps ≤ effectProb T.1 (copies (m + 1) (output 1 2 N X.1)) := by
    unfold effectProb at h1 ⊢
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re, htr] at h1
    simp only [Complex.one_re] at h1
    linarith
  rw [if_neg (by linarith)]
  apply ENNReal.ofReal_le_ofReal
  exact neg_le_neg (Real.logb_le_logb_of_le (by norm_num) (by linarith) hp)

lemma lims (N : Maps 3 3) (hN : IsChannel (N : Superop (Fin 3) (Fin 3)))
    (Ui Vo : Matrix.unitaryGroup (Fin 3) ℂ)
    (h : ∀ X, N X = (Vo : Mat (Fin 3)) * wernerHolevo 3 ((Ui : Mat (Fin 3)) * X * (Ui : Mat (Fin 3))ᴴ) *
      (Vo : Mat (Fin 3))ᴴ) (eps : ℝ) (he1 : eps < 1) :
    liminf (fun m => blockRate 1 (MU 3) N 2 (MESProbe 3) m eps) atTop = 0 ∧
    limsup (fun m => blockRate 1 (MU 3) N 2 (MESProbe 3) m eps) atTop = 0 := by
  set C := ENNReal.ofReal (-Real.logb 2 (1 - eps))
  have ht : Tendsto (fun m : ℕ => C / ((2 * (m + 1) : ℕ) : ℝ≥0∞)) atTop (𝓝 0) := by
    have h0 := ENNReal.tendsto_inv_nat_nhds_zero.comp
      ((tendsto_id.const_mul_atTop' (by norm_num : 0 < 2)).comp (tendsto_add_atTop_nat 1))
    have h2 := ENNReal.Tendsto.const_mul h0 (Or.inr ENNReal.ofReal_ne_top) (a := C)
    rw [mul_zero] at h2
    refine h2.congr fun m => ?_
    simp [div_eq_mul_inv]
  have hle : ∀ᶠ m in atTop, blockRate 1 (MU 3) N 2 (MESProbe 3) m eps ≤
      C / ((2 * (m + 1) : ℕ) : ℝ≥0∞) := Eventually.of_forall fun m => rate_bound2 N hN Ui Vo h m eps he1
  constructor
  · refine le_antisymm ?_ zero_le
    calc _ ≤ liminf (fun m : ℕ => C / ((2 * (m + 1) : ℕ) : ℝ≥0∞)) atTop := liminf_le_liminf hle
      _ = 0 := ht.liminf_eq
  · refine le_antisymm ?_ zero_le
    calc _ ≤ limsup (fun m : ℕ => C / ((2 * (m + 1) : ℕ) : ℝ≥0∞)) atTop := limsup_le_limsup hle
      _ = 0 := ht.limsup_eq

theorem main2 (N : Maps 3 3) (hN : IsChannel (N : Superop (Fin 3) (Fin 3)))
    (he : UnitaryEquivalent (wernerHolevo 3) N) :
    HasSteinValue (blockRate 1 (MU 3) N 2 (MESProbe 3)) 0 ∧
    operational (blockRate 1 (MU 3) N 2 (MESProbe 3)) = 0 := by
  obtain ⟨Ui, Vo, h⟩ := he
  have hev : ∀ᶠ eps in 𝓝[Set.Ioo (0:ℝ) 1] 0,
      liminf (fun m => blockRate 1 (MU 3) N 2 (MESProbe 3) m eps) atTop = 0 ∧
      limsup (fun m => blockRate 1 (MU 3) N 2 (MESProbe 3) m eps) atTop = 0 :=
    eventually_nhdsWithin_of_forall fun eps he => lims N hN Ui Vo h eps he.2
  have : NeBot (𝓝[Set.Ioo (0:ℝ) 1] 0) := left_nhdsWithin_Ioo_neBot one_pos
  refine ⟨⟨tendsto_const_nhds.congr' (hev.mono fun eps h => h.1.symm),
    tendsto_const_nhds.congr' (hev.mono fun eps h => h.2.symm)⟩, ?_⟩
  unfold operational
  rw [liminf_congr (hev.mono fun eps h => h.1 : ∀ᶠ eps in 𝓝[Set.Ioo (0:ℝ) 1] 0, _ = (fun _ => (0:ℝ≥0∞)) eps)]
  exact liminf_const 0

end X4P60

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P60

section
attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution (N : Maps 3 3) (hN : IsChannel N)
    (he : UnitaryEquivalent (wernerHolevo 3) N) : HasSteinValue (blockRate 1 (MU 3) N 2 (MESProbe 3)) 0 ∧
    operational (blockRate 1 (MU 3) N 2 (MESProbe 3)) = 0 := by
  convert X4P60.main2 N (by convert hN) he

end
