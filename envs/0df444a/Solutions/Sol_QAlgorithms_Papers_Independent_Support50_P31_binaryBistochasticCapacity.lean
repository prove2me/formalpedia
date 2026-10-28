-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P31.binaryBistochasticCapacity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T14:02:17.446719+00:00
-- url     : https://prove2.me/submissions/62009c6c-ff8b-4710-a5c8-c0b6164920d5

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P31

noncomputable section

open Filter Asymptotics
open scoped ComplexConjugate ENNReal Matrix ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.X7L2

open QAlgorithms.Papers.Independent.Information100.P56 (entropy holevo average)
open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble)
open QAlgorithms.Papers.Independent.Gap48.P03 (holevoQuantity holevoScore)

lemma cfc_trace {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

/-- trace of cfc for a unitarily diagonalized hermitian matrix -/
lemma cfc_trace_conj {n : Type*} [Fintype n] [DecidableEq n] (M W : Matrix n n ℂ) (d : n → ℝ)
    (hM : M.IsHermitian) (hW : Wᴴ * W = 1)
    (hMd : M = W * Matrix.diagonal (fun i => (d i : ℂ)) * Wᴴ) (f : ℝ → ℝ) :
    (cfc f M).trace = ∑ i, ((f (d i) : ℝ) : ℂ) := by
  rw [cfc_trace hM]
  have hcp : M.charpoly = (Matrix.diagonal (fun i => (d i : ℂ))).charpoly := by
    rw [hMd, Matrix.mul_assoc, Matrix.charpoly_mul_comm, Matrix.mul_assoc, hW, Matrix.mul_one]
  have h1 := hM.roots_charpoly_eq_eigenvalues
  rw [hcp, Matrix.charpoly_diagonal, Polynomial.roots_prod _ _ (by
    simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])] at h1
  simp only [Polynomial.roots_X_sub_C] at h1
  have h2 : Multiset.map (fun i => (d i : ℂ)) Finset.univ.val =
      Multiset.map (fun i => ((hM.eigenvalues i : ℝ) : ℂ)) Finset.univ.val := by
    have := h1
    rw [Multiset.bind_singleton] at this
    exact this
  have h3 := congrArg (fun m => (Multiset.map (fun z : ℂ => ((f z.re : ℝ) : ℂ)) m).sum) h2
  simp only [Multiset.map_map, Function.comp_def, Complex.ofReal_re] at h3
  exact h3.symm

lemma entropy_eq {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian) :
    entropy Y = -∑ i, hY.eigenvalues i * Real.log (hY.eigenvalues i) := by
  unfold entropy
  rw [cfc_trace hY]
  simp

lemma entropy_conj {n : Type*} [Fintype n] [DecidableEq n] (M W : Matrix n n ℂ) (d : n → ℝ)
    (hM : M.IsHermitian) (hW : Wᴴ * W = 1)
    (hMd : M = W * Matrix.diagonal (fun i => (d i : ℂ)) * Wᴴ) :
    entropy M = -∑ i, d i * Real.log (d i) := by
  unfold entropy
  rw [cfc_trace_conj M W d hM hW hMd]
  simp

lemma spectral {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian) :
    Y = (hY.eigenvectorUnitary : Matrix n n ℂ) *
      Matrix.diagonal (fun i => ((hY.eigenvalues i : ℝ) : ℂ)) *
      (hY.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
  have hs := hY.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  exact hs

lemma unitary_ctm {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian) :
    (hY.eigenvectorUnitary : Matrix n n ℂ)ᴴ * (hY.eigenvectorUnitary : Matrix n n ℂ) = 1 :=
  Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2

lemma eig_sum {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (htr : Y.trace = 1) : ∑ i, hY.eigenvalues i = 1 := by
  have := hY.trace_eq_sum_eigenvalues
  rw [htr] at this
  have h2 := congrArg Complex.re this
  simp at h2
  exact_mod_cast h2.symm

lemma term_le (D μ : ℝ) (hD : 0 < D) (hμ : 0 ≤ μ) :
    -(μ * Real.log μ) - μ * Real.log D ≤ 1 / D - μ := by
  rcases hμ.eq_or_lt with h | h
  · subst h; simp; positivity
  · have h1 := Real.log_le_sub_one_of_pos (show 0 < 1 / (D * μ) by positivity)
    rw [one_div, Real.log_inv, Real.log_mul hD.ne' h.ne'] at h1
    have h2 : μ * ((D * μ)⁻¹ - 1) = 1 / D - μ := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left h1 h.le]

lemma ent_le_log {n : Type*} [Fintype n] (μ : n → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (hs : ∑ i, μ i = 1) (hn : 0 < Fintype.card n) :
    -∑ i, μ i * Real.log (μ i) ≤ Real.log (Fintype.card n) := by
  have hD : (0:ℝ) < Fintype.card n := by exact_mod_cast hn
  have key : ∑ i, (-(μ i * Real.log (μ i)) - μ i * Real.log (Fintype.card n)) ≤
      ∑ _i : n, (1 / (Fintype.card n : ℝ)) - ∑ i, μ i := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun i _ => term_le _ _ hD (hμ i)
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hs, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at key
  rw [mul_one_div_cancel hD.ne'] at key
  rw [← Finset.sum_neg_distrib]
  linarith

lemma ent_bounds {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (ρ : Matrix n n ℂ) (h : IsDensityMatrix ρ) :
    0 ≤ entropy ρ ∧ entropy ρ ≤ Real.log (Fintype.card n) := by
  have hH := h.1.isHermitian
  have hsum := eig_sum hH h.2
  have hnn : ∀ i, 0 ≤ hH.eigenvalues i := fun i => h.1.eigenvalues_nonneg i
  have hle : ∀ i, hH.eigenvalues i ≤ 1 := fun i => by
    rw [← hsum]; exact Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
  rw [entropy_eq hH]
  constructor
  · rw [neg_nonneg]; apply Finset.sum_nonpos; intro i _
    exact mul_nonpos_of_nonneg_of_nonpos (hnn i) (Real.log_nonpos (hnn i) (hle i))
  · exact ent_le_log _ hnn hsum Fintype.card_pos

lemma kraus_density {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] {m : ℕ}
    (E : Fin m → Matrix κ ι ℂ) (hE : IsKrausFamily E) (ρ : Matrix ι ι ℂ) (hρ : IsDensityMatrix ρ) :
    IsDensityMatrix (krausApply E ρ) := by
  refine ⟨Matrix.posSemidef_sum _ fun j _ => hρ.1.mul_mul_conjTranspose_same (E j), ?_⟩
  unfold krausApply
  rw [Matrix.trace_sum]
  simp_rw [Matrix.trace_mul_cycle (E _) ρ]
  rw [← Matrix.trace_sum, ← Finset.sum_mul]
  rw [show (∑ j, (E j)ᴴ * E j) = 1 from hE, one_mul, hρ.2]

lemma chan_density {ι : Type*} [Fintype ι] [DecidableEq ι] (Φ : Superop ι ι) (hΦ : IsChannel Φ)
    (ρ : Matrix ι ι ℂ) (hρ : IsDensityMatrix ρ) : IsDensityMatrix (Φ ρ) := by
  obtain ⟨m, E, hE, hEq⟩ := hΦ
  rw [hEq]; exact kraus_density E hE ρ hρ

lemma chan_sub {ι : Type*} [Fintype ι] [DecidableEq ι] (Φ : Superop ι ι) (hΦ : IsChannel Φ)
    (X Y : Matrix ι ι ℂ) : Φ (X - Y) = Φ X - Φ Y := by
  obtain ⟨m, E, hE, hEq⟩ := hΦ
  rw [hEq, hEq, hEq]
  unfold krausApply
  simp only [Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]

/-- the qubit flip `1 - X` -/
lemma flip_density {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : IsDensityMatrix X) :
    IsDensityMatrix (1 - X) := by
  have hH := hX.1.isHermitian
  have hsum := eig_sum hH hX.2
  have hnn : ∀ i, 0 ≤ hH.eigenvalues i := fun i => hX.1.eigenvalues_nonneg i
  have hle : ∀ i, hH.eigenvalues i ≤ 1 := fun i => by
    rw [← hsum]; exact Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
  set U := (hH.eigenvectorUnitary : Matrix (Fin 2) (Fin 2) ℂ)
  have hU : U * Uᴴ = 1 := Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
  have hrep : 1 - X = U * Matrix.diagonal (fun i => ((1 - hH.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
    conv_lhs => rw [spectral hH]
    have : Matrix.diagonal (fun i => ((1 - hH.eigenvalues i : ℝ) : ℂ)) =
        1 - Matrix.diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) := by
      ext i j; by_cases h : i = j <;> simp [Matrix.diagonal, Matrix.one_apply, h]
    rw [this, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU]
  refine ⟨?_, ?_⟩
  · rw [hrep]
    apply Matrix.PosSemidef.mul_mul_conjTranspose_same
    rw [Matrix.posSemidef_diagonal_iff]
    intro i
    have := hle i
    exact_mod_cast (show (0:ℝ) ≤ 1 - hH.eigenvalues i by linarith)
  · rw [Matrix.trace_sub, hX.2]; simp [Matrix.trace_one]; norm_num

lemma flip_entropy {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : IsDensityMatrix X) :
    entropy (1 - X) = entropy X := by
  have hH := hX.1.isHermitian
  have hsum := eig_sum hH hX.2
  set U := (hH.eigenvectorUnitary : Matrix (Fin 2) (Fin 2) ℂ)
  have hU : U * Uᴴ = 1 := Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
  have hrep : 1 - X = U * Matrix.diagonal (fun i => ((1 - hH.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
    conv_lhs => rw [spectral hH]
    have : Matrix.diagonal (fun i => ((1 - hH.eigenvalues i : ℝ) : ℂ)) =
        1 - Matrix.diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) := by
      ext i j; by_cases h : i = j <;> simp [Matrix.diagonal, Matrix.one_apply, h]
    rw [this, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU]
  rw [entropy_conj (1 - X) U _ (flip_density hX).1.isHermitian (unitary_ctm hH) hrep,
    entropy_eq hH]
  rw [Fin.sum_univ_two] at hsum ⊢
  rw [Fin.sum_univ_two]
  have h0 : 1 - hH.eigenvalues 0 = hH.eigenvalues 1 := by linarith
  have h1 : 1 - hH.eigenvalues 1 = hH.eigenvalues 0 := by linarith
  rw [h0, h1]; ring

lemma entropy_scalar {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] :
    entropy ((((Fintype.card n : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Matrix n n ℂ)) = Real.log (Fintype.card n) := by
  have hD : (0:ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hM : ((((Fintype.card n : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Matrix n n ℂ)) =
      1 * Matrix.diagonal (fun _ => (((Fintype.card n : ℝ)⁻¹ : ℝ) : ℂ)) * (1 : Matrix n n ℂ)ᴴ := by
    ext i j; by_cases h : i = j <;> simp [Matrix.diagonal, Matrix.one_apply, h]
  have hH : ((((Fintype.card n : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Matrix n n ℂ)).IsHermitian := by
    rw [hM]; simp [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  rw [entropy_conj _ 1 _ hH (by simp) hM]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Real.log_inv]
  field_simp

open QAlgorithms.Papers.Independent.Support50.P31 (nuH)

lemma avg_density {I : Type} [Fintype I] [DecidableEq I] {k : ℕ} (P : Fin k → ℝ)
    (hP : ∀ x, 0 ≤ P x) (hs : ∑ x, P x = 1) (W : Fin k → Matrix I I ℂ)
    (hW : ∀ x, IsDensityMatrix (W x)) : IsDensityMatrix (average W P) := by
  unfold average
  refine ⟨Matrix.posSemidef_sum _ fun x _ => ?_, ?_⟩
  · exact (hW x).1.smul (by exact_mod_cast hP x)
  · rw [Matrix.trace_sum]
    simp only [Matrix.trace_smul, (hW _).2, smul_eq_mul, mul_one]
    exact_mod_cast hs

lemma nuH_bdd {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] (N : Superop I I)
    (hN : ∀ ρ, IsDensityMatrix ρ → IsDensityMatrix (N ρ)) :
    BddBelow (Set.range fun X : {X : Matrix I I ℂ // IsDensityMatrix X} => entropy (N X.val)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨X, rfl⟩
  exact (ent_bounds _ (hN _ X.2)).1

lemma exists_density (I : Type) [Fintype I] [DecidableEq I] [Nonempty I] :
    IsDensityMatrix ((((Fintype.card I : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Matrix I I ℂ)) := by
  have hD : (0:ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  refine ⟨Matrix.PosSemidef.one.smul (by exact_mod_cast (inv_pos.2 hD).le), ?_⟩
  rw [Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
  push_cast
  field_simp

lemma nuH_le {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] (N : Superop I I)
    (hN : ∀ ρ, IsDensityMatrix ρ → IsDensityMatrix (N ρ)) (ρ : Matrix I I ℂ)
    (hρ : IsDensityMatrix ρ) : nuH N ≤ entropy (N ρ) := by
  unfold nuH
  exact csInf_le (nuH_bdd N hN) ⟨⟨ρ, hρ⟩, rfl⟩

lemma score_le {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] (N : Superop I I)
    (hN : ∀ ρ, IsDensityMatrix ρ → IsDensityMatrix (N ρ)) (e : Ensemble I) :
    holevoScore N e ≤ Real.log (Fintype.card I) - nuH N := by
  unfold holevoScore holevo
  have h1 := (ent_bounds _ (avg_density e.prob e.nonneg e.total _ fun x => hN _ (e.density x))).2
  have h2 : nuH N ≤ ∑ x, e.prob x * entropy (N (e.state x)) := by
    calc nuH N = ∑ x, e.prob x * nuH N := by rw [← Finset.sum_mul, e.total, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun x _ =>
          mul_le_mul_of_nonneg_left (nuH_le N hN _ (e.density x)) (e.nonneg x)
  linarith

def oneEns (I : Type) [Fintype I] [DecidableEq I] [Nonempty I] : Ensemble I where
  size := 1
  prob := fun _ => 1
  state := fun _ => (((Fintype.card I : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Matrix I I ℂ)
  nonneg := fun _ => zero_le_one
  total := by simp
  density := fun _ => exists_density I

lemma hq_le {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] (N : Superop I I)
    (hN : ∀ ρ, IsDensityMatrix ρ → IsDensityMatrix (N ρ)) :
    holevoQuantity N ≤ Real.log (Fintype.card I) - nuH N := by
  unfold holevoQuantity
  refine csSup_le ⟨_, oneEns I, rfl⟩ ?_
  rintro _ ⟨e, rfl⟩
  exact score_le N hN e

lemma le_hq {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] (N : Superop I I)
    (hN : ∀ ρ, IsDensityMatrix ρ → IsDensityMatrix (N ρ)) (e : Ensemble I) :
    holevoScore N e ≤ holevoQuantity N := by
  unfold holevoQuantity
  refine le_csSup ⟨Real.log (Fintype.card I) - nuH N, ?_⟩ ⟨e, rfl⟩
  rintro _ ⟨e', rfl⟩
  exact score_le N hN e'

lemma unital_flip (Φ : Superop (Fin 2) (Fin 2)) (hΦ : IsChannel Φ) (hu : Φ 1 = 1)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) : Φ (1 - ρ) = 1 - Φ ρ := by
  rw [chan_sub Φ hΦ, hu]

def flipEns (ρ : Matrix (Fin 2) (Fin 2) ℂ) (hρ : IsDensityMatrix ρ) : Ensemble (Fin 2) where
  size := 2
  prob := fun _ => 1 / 2
  state := ![ρ, 1 - ρ]
  nonneg := fun _ => by norm_num
  total := by simp
  density := fun x => by
    fin_cases x
    · exact hρ
    · exact flip_density hρ

lemma half_one : (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) =
    (((Fintype.card (Fin 2) : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp

theorem clause1 (Phi : Superop (Fin 2) (Fin 2))
    (hPhi : IsChannel Phi) (hunital : Phi 1 = 1) :
    holevoQuantity Phi = Real.log 2 - nuH Phi := by
  have hN := chan_density Phi hPhi
  apply le_antisymm
  · have := hq_le Phi hN
    simpa using this
  · have key : ∀ ρ : {X : Matrix (Fin 2) (Fin 2) ℂ // IsDensityMatrix X},
        Real.log 2 - holevoQuantity Phi ≤ entropy (Phi ρ.val) := by
      rintro ⟨ρ, hρ⟩
      have h := le_hq Phi hN (flipEns ρ hρ)
      have hsc : holevoScore Phi (flipEns ρ hρ) = Real.log 2 - entropy (Phi ρ) := by
        unfold holevoScore holevo average flipEns
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          unital_flip Phi hPhi hunital, flip_entropy (hN ρ hρ)]
        have : (((1 / 2 : ℝ) : ℂ) • Phi ρ + ((1 / 2 : ℝ) : ℂ) • (1 - Phi ρ)) =
            (((Fintype.card (Fin 2) : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
          rw [← half_one, smul_sub, ← add_sub_assoc, add_sub_cancel_left]
          push_cast; norm_num
        rw [this, entropy_scalar]
        simp; ring
      dsimp only
      linarith
    haveI : Nonempty {X : Matrix (Fin 2) (Fin 2) ℂ // IsDensityMatrix X} :=
      ⟨⟨_, exists_density (Fin 2)⟩⟩
    have := le_csInf (Set.range_nonempty _) (by rintro _ ⟨ρ, rfl⟩; exact key ρ)
    unfold nuH
    linarith

/-! ### n-fold Kronecker products -/

def piKron {n : ℕ} {ι : Type} (A : Fin n → Matrix ι ι ℂ) : Matrix (Fin n → ι) (Fin n → ι) ℂ :=
  fun y y' => ∏ i, A i (y i) (y' i)

lemma piKron_mul {n : ℕ} {ι : Type} [Fintype ι] (A B : Fin n → Matrix ι ι ℂ) :
    piKron A * piKron B = piKron (fun i => A i * B i) := by
  ext y w
  simp only [piKron, Matrix.mul_apply]
  rw [Fintype.prod_sum (fun i c => A i (y i) c * B i c (w i))]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.prod_mul_distrib]

lemma piKron_ct {n : ℕ} {ι : Type} (A : Fin n → Matrix ι ι ℂ) :
    (piKron A)ᴴ = piKron (fun i => (A i)ᴴ) := by
  ext y w
  simp only [piKron, Matrix.conjTranspose_apply, star_prod]

lemma piKron_one {n : ℕ} {ι : Type} [DecidableEq ι] :
    piKron (fun _ : Fin n => (1 : Matrix ι ι ℂ)) = 1 := by
  ext y w
  simp only [piKron, Matrix.one_apply]
  by_cases h : y = w
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, y i ≠ w i := by
      by_contra hc; push_neg at hc; exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

lemma piKron_diag {n : ℕ} {ι : Type} [DecidableEq ι] (d : Fin n → ι → ℂ) :
    piKron (fun i => Matrix.diagonal (d i)) = Matrix.diagonal (fun s => ∏ i, d i (s i)) := by
  ext y w
  simp only [piKron, Matrix.diagonal_apply]
  by_cases h : y = w
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, y i ≠ w i := by
      by_contra hc; push_neg at hc; exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

lemma piKron_trace {n : ℕ} {ι : Type} [Fintype ι] (A : Fin n → Matrix ι ι ℂ) :
    (piKron A).trace = ∏ i, (A i).trace := by
  simp only [Matrix.trace, Matrix.diag, piKron]
  rw [Fintype.prod_sum (fun i c => A i c c)]

lemma piKron_sum {n : ℕ} {ι : Type} {m : Fin n → Type} [∀ i, Fintype (m i)]
    (Z : (i : Fin n) → m i → Matrix ι ι ℂ) :
    ∑ k : ((i : Fin n) → m i), piKron (fun i => Z i (k i)) = piKron (fun i => ∑ j, Z i j) := by
  ext y w
  simp only [piKron, Matrix.sum_apply]
  rw [Fintype.prod_sum (fun i j => Z i j (y i) (w i))]

lemma piKron_smul_sum {n : ℕ} {ι : Type} {m : Fin n → Type} [∀ i, Fintype (m i)] (c : ℂ)
    (Z : (i : Fin n) → m i → Matrix ι ι ℂ) :
    ∑ k : ((i : Fin n) → m i), c • piKron (fun i => Z i (k i)) =
      c • piKron (fun i => ∑ j, Z i j) := by
  rw [← Finset.smul_sum, piKron_sum]

/-- classical entropy additivity for product distributions -/
lemma prod_entropy {n : ℕ} {ι : Type} [Fintype ι] (p : Fin n → ι → ℝ)
    (hs : ∀ i, ∑ t, p i t = 1) :
    ∑ s : Fin n → ι, (∏ i, p i (s i)) * Real.log (∏ i, p i (s i)) =
      ∑ i, ∑ t, p i t * Real.log (p i t) := by
  have h1 : ∀ s : Fin n → ι, (∏ i, p i (s i)) * Real.log (∏ i, p i (s i)) =
      ∑ j, (∏ i, p i (s i)) * Real.log (p j (s j)) := by
    intro s
    rw [← Finset.mul_sum]
    by_cases h : ∀ i, p i (s i) ≠ 0
    · rw [Real.log_prod (fun i hi => h i)]
    · push_neg at h
      obtain ⟨i, hi⟩ := h
      rw [Finset.prod_eq_zero (Finset.mem_univ i) hi]; simp
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h2 : ∀ s : Fin n → ι, (∏ i, p i (s i)) * Real.log (p j (s j)) =
      ∏ i, (if i = j then p i (s i) * Real.log (p i (s i)) else p i (s i)) := by
    intro s
    have : ∀ i, (if i = j then p i (s i) * Real.log (p i (s i)) else p i (s i)) =
        p i (s i) * (if i = j then Real.log (p i (s i)) else 1) := by
      intro i; split_ifs <;> ring
    simp_rw [this]
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ j]
    simp
  simp_rw [h2]
  rw [← Fintype.prod_sum (fun i t => if i = j then p i t * Real.log (p i t) else p i t)]
  have : ∀ i, (∑ t, if i = j then p i t * Real.log (p i t) else p i t) =
      if i = j then ∑ t, p j t * Real.log (p j t) else 1 := by
    intro i; split_ifs with h
    · subst h; rfl
    · exact hs i
  simp_rw [this]
  rw [Finset.prod_ite_eq' Finset.univ j]
  simp

lemma entropy_piKron {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (Y : Fin n → Matrix ι ι ℂ)
    (hY : ∀ i, (Y i).IsHermitian) (htr : ∀ i, (Y i).trace = 1) :
    entropy (piKron Y) = ∑ i, entropy (Y i) := by
  set U : Fin n → Matrix ι ι ℂ := fun i => ((hY i).eigenvectorUnitary : Matrix ι ι ℂ)
  set D : Fin n → Matrix ι ι ℂ :=
    fun i => Matrix.diagonal (fun t => (((hY i).eigenvalues t : ℝ) : ℂ))
  have hrep : piKron Y = piKron U * Matrix.diagonal
      (fun s => (((∏ i, (hY i).eigenvalues (s i)) : ℝ) : ℂ)) * (piKron U)ᴴ := by
    have : Matrix.diagonal (fun s => (((∏ i, (hY i).eigenvalues (s i)) : ℝ) : ℂ)) = piKron D := by
      rw [piKron_diag]; push_cast; rfl
    rw [this, piKron_ct, piKron_mul, piKron_mul]
    congr 1; funext i; exact spectral (hY i)
  have hW : (piKron U)ᴴ * piKron U = 1 := by
    rw [piKron_ct, piKron_mul]
    have : (fun i => (U i)ᴴ * U i) = fun _ => (1 : Matrix ι ι ℂ) := by
      funext i; exact unitary_ctm (hY i)
    rw [this, piKron_one]
  have hH : (piKron Y).IsHermitian := by
    unfold Matrix.IsHermitian; rw [piKron_ct]; congr 1; funext i; exact hY i
  rw [entropy_conj _ _ _ hH hW hrep]
  rw [prod_entropy (fun i t => (hY i).eigenvalues t) (fun i => eig_sum (hY i) (htr i))]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [entropy_eq (hY i)]

lemma piKron_density {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (Y : Fin n → Matrix ι ι ℂ)
    (hY : ∀ i, IsDensityMatrix (Y i)) : IsDensityMatrix (piKron Y) := by
  have hH : ∀ i, (Y i).IsHermitian := fun i => (hY i).1.isHermitian
  set U : Fin n → Matrix ι ι ℂ := fun i => ((hH i).eigenvectorUnitary : Matrix ι ι ℂ)
  set D : Fin n → Matrix ι ι ℂ :=
    fun i => Matrix.diagonal (fun t => (((hH i).eigenvalues t : ℝ) : ℂ))
  have hrep : piKron Y = piKron U * Matrix.diagonal
      (fun s => (((∏ i, (hH i).eigenvalues (s i)) : ℝ) : ℂ)) * (piKron U)ᴴ := by
    have : Matrix.diagonal (fun s => (((∏ i, (hH i).eigenvalues (s i)) : ℝ) : ℂ)) = piKron D := by
      rw [piKron_diag]; push_cast; rfl
    rw [this, piKron_ct, piKron_mul, piKron_mul]
    congr 1; funext i; exact spectral (hH i)
  refine ⟨?_, ?_⟩
  · rw [hrep]
    apply Matrix.PosSemidef.mul_mul_conjTranspose_same
    rw [Matrix.posSemidef_diagonal_iff]
    intro s
    have : (0:ℝ) ≤ ∏ i, (hH i).eigenvalues (s i) :=
      Finset.prod_nonneg fun i _ => (hY i).1.eigenvalues_nonneg _
    exact_mod_cast this
  · rw [piKron_trace]; simp [(hY _).2]

/-! ### the product channel -/

lemma kraus_single {ι κ : Type} [Fintype ι] [DecidableEq ι] {m : ℕ} (E : Fin m → Matrix κ ι ℂ)
    (a b : ι) (c d : κ) :
    krausApply E (Matrix.single a b 1) c d = ∑ j, E j c a * star (E j d b) := by
  simp [krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.single_apply,
    Matrix.conjTranspose_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', ite_mul]

lemma pi_kraus {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {m : Fin n → ℕ}
    (E : (i : Fin n) → Fin (m i) → Matrix ι ι ℂ) (Psi : Fin n → Superop ι ι)
    (hEq : ∀ i ρ, Psi i ρ = krausApply (E i) ρ) (X : Matrix (Fin n → ι) (Fin n → ι) ℂ) :
    piSuperop Psi X = ∑ k : ((i : Fin n) → Fin (m i)),
      piKron (fun i => E i (k i)) * X * (piKron (fun i => E i (k i)))ᴴ := by
  ext y y'
  simp only [piSuperop, Matrix.of_apply, hEq, kraus_single, Matrix.sum_apply, Matrix.mul_apply,
    piKron_ct, piKron, Matrix.conjTranspose_apply]
  simp_rw [Fintype.prod_sum]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  conv_rhs => arg 2; ext x'; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x' _ => ?_
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

lemma pi_density {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (Psi : Fin n → Superop ι ι)
    (hPsi : ∀ i, IsChannel (Psi i)) (X : Matrix (Fin n → ι) (Fin n → ι) ℂ)
    (hX : IsDensityMatrix X) : IsDensityMatrix (piSuperop Psi X) := by
  choose m E hE hEq using hPsi
  rw [pi_kraus E Psi hEq X]
  refine ⟨Matrix.posSemidef_sum _ fun k _ => hX.1.mul_mul_conjTranspose_same _, ?_⟩
  rw [Matrix.trace_sum]
  simp_rw [Matrix.trace_mul_cycle (piKron _) X]
  rw [← Matrix.trace_sum, ← Finset.sum_mul]
  have : ∑ k : ((i : Fin n) → Fin (m i)), (piKron (fun i => E i (k i)))ᴴ *
      piKron (fun i => E i (k i)) = 1 := by
    simp_rw [piKron_ct, piKron_mul]
    rw [piKron_sum (fun i j => (E i j)ᴴ * E i j)]
    have h1 : (fun i => ∑ j, (E i j)ᴴ * E i j) = fun _ => (1 : Matrix ι ι ℂ) := by
      funext i; exact hE i
    rw [h1, piKron_one]
  rw [this, one_mul, hX.2]

lemma pi_on_kron {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (Psi : Fin n → Superop ι ι)
    (hPsi : ∀ i, IsChannel (Psi i)) (ρ : Fin n → Matrix ι ι ℂ) :
    piSuperop Psi (piKron ρ) = piKron (fun i => Psi i (ρ i)) := by
  choose m E hE hEq using hPsi
  rw [pi_kraus E Psi hEq]
  simp_rw [piKron_ct, piKron_mul]
  rw [piKron_sum (fun i j => E i j * ρ i * (E i j)ᴴ)]
  congr 1; funext i
  rw [hEq]; rfl

/-! ### clause 2 -/

def flipState {n : ℕ} (ρ : Fin n → Matrix (Fin 2) (Fin 2) ℂ) (s : Fin n → Fin 2) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  piKron (fun i => if s i = 0 then ρ i else 1 - ρ i)

lemma flipState_density {n : ℕ} (ρ : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hρ : ∀ i, IsDensityMatrix (ρ i)) (s : Fin n → Fin 2) : IsDensityMatrix (flipState ρ s) := by
  apply piKron_density
  intro i
  split_ifs
  · exact hρ i
  · exact flip_density (hρ i)

lemma card_pow (n : ℕ) : Fintype.card (Fin n → Fin 2) = 2 ^ n := by simp

def prodEns {n : ℕ} (ρ : Fin n → Matrix (Fin 2) (Fin 2) ℂ) (hρ : ∀ i, IsDensityMatrix (ρ i)) :
    Ensemble (Fin n → Fin 2) where
  size := 2 ^ n
  prob := fun _ => ((2 : ℝ) ^ n)⁻¹
  state := fun k => flipState ρ ((Fintype.equivFinOfCardEq (card_pow n)).symm k)
  nonneg := fun _ => by positivity
  total := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  density := fun k => flipState_density ρ hρ _

theorem clause2 (n : ℕ) (hn : 0 < n) (Psi : Fin n → Superop (Fin 2) (Fin 2))
    (hPsi : ∀ i, IsChannel (Psi i) ∧ Psi i 1 = 1)
    (hadd : nuH (piSuperop Psi) = ∑ i, nuH (Psi i)) :
    holevoQuantity (piSuperop Psi) = ∑ i, holevoQuantity (Psi i) := by
  have hC : ∀ i, IsChannel (Psi i) := fun i => (hPsi i).1
  have hN := pi_density Psi hC
  rw [Finset.sum_congr rfl (fun i _ => clause1 (Psi i) (hPsi i).1 (hPsi i).2)]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hlog : Real.log (Fintype.card (Fin n → Fin 2)) = n * Real.log 2 := by
    rw [card_pow]; push_cast; rw [Real.log_pow]
  apply le_antisymm
  · have := hq_le _ hN
    rw [hlog, hadd] at this
    linarith
  · apply le_of_forall_pos_le_add
    intro ε hε
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn
    have hex : ∀ i, ∃ ρ : {X : Matrix (Fin 2) (Fin 2) ℂ // IsDensityMatrix X},
        entropy (Psi i ρ.val) < nuH (Psi i) + ε / n := by
      intro i
      haveI : Nonempty {X : Matrix (Fin 2) (Fin 2) ℂ // IsDensityMatrix X} :=
        ⟨⟨_, exists_density (Fin 2)⟩⟩
      have hlt : nuH (Psi i) < nuH (Psi i) + ε / n := by
        have : 0 < ε / n := div_pos hε hnpos
        linarith
      obtain ⟨_, ⟨ρ, rfl⟩, h⟩ := exists_lt_of_csInf_lt (Set.range_nonempty _) hlt
      exact ⟨ρ, h⟩
    choose ρ hρ using hex
    set e := prodEns (fun i => (ρ i).val) (fun i => (ρ i).2) with he
    have hsc := le_hq _ hN e
    have hX : ∀ i, IsDensityMatrix (Psi i (ρ i).val) := fun i => chan_density _ (hC i) _ (ρ i).2
    have hout : ∀ s : Fin n → Fin 2, piSuperop Psi (flipState (fun i => (ρ i).val) s) =
        piKron (fun i => (fun t : Fin 2 => if t = 0 then Psi i (ρ i).val else 1 - Psi i (ρ i).val)
          (s i)) := by
      intro s
      unfold flipState
      rw [pi_on_kron Psi hC]
      congr 1; funext i
      dsimp only
      split_ifs
      · rfl
      · exact unital_flip _ (hC i) (hPsi i).2 _
    have hent : ∀ s : Fin n → Fin 2,
        entropy (piSuperop Psi (flipState (fun i => (ρ i).val) s)) =
          ∑ i, entropy (Psi i (ρ i).val) := by
      intro s
      rw [hout, entropy_piKron]
      · refine Finset.sum_congr rfl fun i _ => ?_
        dsimp only
        split_ifs
        · rfl
        · exact flip_entropy (hX i)
      · intro i; dsimp only; split_ifs
        · exact (hX i).1.isHermitian
        · exact (flip_density (hX i)).1.isHermitian
      · intro i; dsimp only; split_ifs
        · exact (hX i).2
        · exact (flip_density (hX i)).2
    have havg : average (fun k => piSuperop Psi (e.state k)) e.prob =
        (((Fintype.card (Fin n → Fin 2) : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) := by
      unfold average
      rw [he]
      change ∑ k : Fin (2 ^ n), ((((2 : ℝ) ^ n)⁻¹ : ℝ) : ℂ) • piSuperop Psi
        (flipState (fun i => (ρ i).val) ((Fintype.equivFinOfCardEq (card_pow n)).symm k)) = _
      rw [Equiv.sum_comp (Fintype.equivFinOfCardEq (card_pow n)).symm
        (fun s => ((((2 : ℝ) ^ n)⁻¹ : ℝ) : ℂ) • piSuperop Psi (flipState (fun i => (ρ i).val) s))]
      simp_rw [hout]
      have hps := piKron_smul_sum (m := fun _ => Fin 2) ((((2 : ℝ) ^ n)⁻¹ : ℝ) : ℂ)
        (fun i (t : Fin 2) => if t = 0 then Psi i (ρ i).val else 1 - Psi i (ρ i).val)
      beta_reduce at hps
      rw [hps]
      have h1 : (fun i => ∑ j : Fin 2, (if j = 0 then Psi i (ρ i).val else 1 - Psi i (ρ i).val)) =
          fun _ => (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
        funext i
        rw [Fin.sum_univ_two]; simp
      rw [h1, piKron_one, card_pow]
      push_cast; rfl
    have hscore : holevoScore (piSuperop Psi) e =
        n * Real.log 2 - ∑ i, entropy (Psi i (ρ i).val) := by
      unfold holevoScore holevo
      rw [havg, entropy_scalar, hlog]
      congr 1
      rw [he]
      change ∑ k : Fin (2 ^ n), ((2 : ℝ) ^ n)⁻¹ * entropy (piSuperop Psi
        (flipState (fun i => (ρ i).val) ((Fintype.equivFinOfCardEq (card_pow n)).symm k))) = _
      simp_rw [hent]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
      push_cast; ring
    have hsum : ∑ i, entropy (Psi i (ρ i).val) ≤ ∑ i, nuH (Psi i) + ε := by
      calc ∑ i, entropy (Psi i (ρ i).val) ≤ ∑ i, (nuH (Psi i) + ε / n) :=
            Finset.sum_le_sum fun i _ => (hρ i).le
        _ = ∑ i, nuH (Psi i) + ε := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul]
            field_simp
    rw [hscore] at hsc
    linarith

end QAlgorithms.X7L2

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P31
  QAlgorithms.Papers.Independent.Gap48.P03 in
theorem solution (Phi : Superop (Fin 2) (Fin 2))
    (hPhi : IsChannel Phi) (hunital : Phi 1 = 1) :
    holevoQuantity Phi = Real.log 2 - nuH Phi ∧
    ∀ (n : ℕ) (_hn : 0 < n) (Psi : Fin n → Superop (Fin 2) (Fin 2)),
      (∀ i, IsChannel (Psi i) ∧ Psi i 1 = 1) →
      nuH (piSuperop Psi) = ∑ i, nuH (Psi i) →
      holevoQuantity (piSuperop Psi) = ∑ i, holevoQuantity (Psi i) :=
  ⟨X7L2.clause1 Phi hPhi hunital, fun n hn Psi hPsi hadd => X7L2.clause2 n hn Psi hPsi hadd⟩
