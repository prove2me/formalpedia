-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P18.localIsometricInvariance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T16:27:19.451744+00:00
-- url     : https://prove2.me/submissions/b13ec1ce-5c9e-4d8e-aee7-46ef0b549378

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P18

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P18

open scoped BigOperators ComplexOrder
open Matrix

variable {A B C E K L : Type}
  [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Fintype K] [Fintype L]
  [DecidableEq A] [DecidableEq B]

def x8M (F : K → Matrix C A ℂ) (k : Matrix A A ℂ) : Matrix C C ℂ := ∑ i, F i * k * (F i)ᴴ

def x8L (F : K → Matrix C A ℂ) (G : L → Matrix E B ℂ) (X : Matrix (A × B) (A × B) ℂ) :
    Matrix (C × E) (C × E) ℂ :=
  ∑ i, ∑ j, (kronecker (F i) (G j)) * X * (kronecker (F i) (G j))ᴴ

theorem x8_kron (F : K → Matrix C A ℂ) (G : L → Matrix E B ℂ) (k : Matrix A A ℂ) (l : Matrix B B ℂ) :
    kronecker (x8M F k) (x8M G l) = x8L F G (kronecker k l) := by
  unfold x8M x8L
  simp only [Matrix.kronecker]
  simp_rw [conjTranspose_kronecker, ← mul_kronecker_mul]
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp only [kroneckerMap_apply, Matrix.sum_apply, Finset.sum_mul_sum]

theorem x8_gamma (F : Matrix C A ℂ) (G : Matrix E B ℂ) (Y : Matrix (A × B) (A × B) ℂ) :
    QAlgorithms.Papers.Independent.Information100.P04.gamma (kronecker F G * Y * (kronecker F G)ᴴ) =
      kronecker F (G.map (starRingEnd ℂ)) * QAlgorithms.Papers.Independent.Information100.P04.gamma Y *
        (kronecker F (G.map (starRingEnd ℂ)))ᴴ := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp only [QAlgorithms.Papers.Independent.Information100.P04.gamma, Matrix.mul_apply, Matrix.kronecker,
    conjTranspose_apply, kroneckerMap_apply, map_apply, Fintype.sum_prod_type, Finset.sum_mul,
    star_mul', RCLike.star_def, Complex.conj_conj]
  refine Finset.sum_congr rfl fun x _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => arg 2; ext x1; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun x1 _ => ?_
  refine Finset.sum_congr rfl fun y _ => ?_
  ring


theorem x8_M_herm (F : K → Matrix C A ℂ) (k : Matrix A A ℂ) (hk : k.IsHermitian) :
    (x8M F k).IsHermitian := by
  unfold x8M IsHermitian
  rw [conjTranspose_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hk.eq, Matrix.mul_assoc]

theorem x8_M_trace (F : K → Matrix C A ℂ) (hF : ∑ i, (F i)ᴴ * F i = 1) (k : Matrix A A ℂ) :
    (x8M F k).trace = k.trace := by
  unfold x8M
  rw [trace_sum]
  have : ∀ i, (F i * k * (F i)ᴴ).trace = ((F i)ᴴ * F i * k).trace := by
    intro i
    rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
  simp_rw [this]
  rw [← trace_sum, ← Finset.sum_mul, hF, Matrix.one_mul]

theorem x8_L_add (F : K → Matrix C A ℂ) (G : L → Matrix E B ℂ) (X Y : Matrix (A × B) (A × B) ℂ) :
    x8L F G (X + Y) = x8L F G X + x8L F G Y := by
  simp only [x8L, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]

theorem x8_L_sub (F : K → Matrix C A ℂ) (G : L → Matrix E B ℂ) (X Y : Matrix (A × B) (A × B) ℂ) :
    x8L F G (X - Y) = x8L F G X - x8L F G Y := by
  simp only [x8L, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]

theorem x8_L_psd (F : K → Matrix C A ℂ) (G : L → Matrix E B ℂ) (X : Matrix (A × B) (A × B) ℂ)
    (hX : X.PosSemidef) : (x8L F G X).PosSemidef := by
  unfold x8L
  exact posSemidef_sum _ fun i _ => posSemidef_sum _ fun j _ => hX.mul_mul_conjTranspose_same _

theorem x8_L_herm (F : K → Matrix C A ℂ) (G : L → Matrix E B ℂ) (X : Matrix (A × B) (A × B) ℂ)
    (hX : X.IsHermitian) : (x8L F G X).IsHermitian := by
  unfold x8L IsHermitian
  rw [conjTranspose_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [conjTranspose_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hX.eq, Matrix.mul_assoc]

theorem x8_L_gamma (F : K → Matrix C A ℂ) (G : L → Matrix E B ℂ) (Y : Matrix (A × B) (A × B) ℂ) :
    QAlgorithms.Papers.Independent.Information100.P04.gamma (x8L F G Y) =
      x8L F (fun j => (G j).map (starRingEnd ℂ)) (QAlgorithms.Papers.Independent.Information100.P04.gamma Y) := by
  have hs : ∀ {ι : Type} (s : Finset ι) (f : ι → Matrix (C × E) (C × E) ℂ),
      QAlgorithms.Papers.Independent.Information100.P04.gamma (∑ i ∈ s, f i) =
        ∑ i ∈ s, QAlgorithms.Papers.Independent.Information100.P04.gamma (f i) := by
    intro ι s f
    ext i j
    simp [QAlgorithms.Papers.Independent.Information100.P04.gamma, Matrix.sum_apply]
  unfold x8L
  rw [hs]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hs]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact x8_gamma _ _ _

theorem x8_mono (F : K → Matrix C A ℂ) (G : L → Matrix E B ℂ) (hF : ∑ i, (F i)ᴴ * F i = 1)
    (hG : ∑ j, (G j)ᴴ * G j = 1) (s : Matrix (A × B) (A × B) ℂ) :
    correlationGauge (x8L F G s) ≤ correlationGauge s := by
  unfold correlationGauge
  refine le_sInf ?_
  rintro r ⟨k, l, v, ⟨hk, hl, hv, h1, h2, h3, h4⟩, rfl⟩
  refine sInf_le ⟨x8M F k, x8M G l, x8L F G v,
    ⟨x8_M_herm F k hk, x8_M_herm G l hl, x8_L_herm F G v hv, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [← x8_L_add, x8_L_gamma]; exact x8_L_psd _ _ _ h1
  · rw [← x8_L_sub, x8_L_gamma]; exact x8_L_psd _ _ _ h2
  · rw [x8_kron, ← x8_L_add]; exact x8_L_psd _ _ _ h3
  · rw [x8_kron, ← x8_L_sub]; exact x8_L_psd _ _ _ h4
  · simp only [Matrix.kronecker]
    rw [trace_kronecker, trace_kronecker, x8_M_trace F hF, x8_M_trace G hG]


theorem x8_kraus_sum (F : K → Matrix C A ℂ) (G : L → Matrix E B ℂ) (hF : ∑ i, (F i)ᴴ * F i = 1)
    (hG : ∑ j, (G j)ᴴ * G j = 1) :
    ∑ i, ∑ j, (kronecker (F i) (G j))ᴴ * kronecker (F i) (G j) = 1 := by
  have h : kronecker (∑ i, (F i)ᴴ * F i) (∑ j, (G j)ᴴ * G j) =
      ∑ i, ∑ j, (kronecker (F i) (G j))ᴴ * kronecker (F i) (G j) := by
    simp only [Matrix.kronecker]
    simp_rw [conjTranspose_kronecker, ← mul_kronecker_mul]
    ext ⟨a, b⟩ ⟨a', b'⟩
    simp only [kroneckerMap_apply, Matrix.sum_apply, Finset.sum_mul_sum]
  rw [← h, hF, hG]
  simp only [Matrix.kronecker]
  exact one_kronecker_one

theorem x8_L_trace (F : K → Matrix C A ℂ) (G : L → Matrix E B ℂ) (hF : ∑ i, (F i)ᴴ * F i = 1)
    (hG : ∑ j, (G j)ᴴ * G j = 1) (X : Matrix (A × B) (A × B) ℂ) :
    (x8L F G X).trace = X.trace := by
  unfold x8L
  have : ∀ (M : Matrix (C × E) (A × B) ℂ), (M * X * Mᴴ).trace = (Mᴴ * M * X).trace := by
    intro M
    rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
  simp_rw [trace_sum, this, ← trace_sum, ← Finset.sum_mul, x8_kraus_sum F G hF hG, Matrix.one_mul]

end QAlgorithms.Papers.Independent.Dependency50.P18

end


noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P18

open scoped BigOperators ComplexOrder
open Matrix

variable {A B C E K L : Type}
  [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Fintype K] [Fintype L]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq E]

theorem x8_L_channel (F : K → Matrix C A ℂ) (G : L → Matrix E B ℂ) (hF : ∑ i, (F i)ᴴ * F i = 1)
    (hG : ∑ j, (G j)ᴴ * G j = 1) : QAlgorithms.IsChannel (x8L F G) := by
  let e := Fintype.equivFin (K × L)
  refine ⟨Fintype.card (K × L), fun n => kronecker (F (e.symm n).1) (G (e.symm n).2), ?_, ?_⟩
  · unfold QAlgorithms.IsKrausFamily
    rw [← x8_kraus_sum F G hF hG, ← Fintype.sum_prod_type']
    exact Equiv.sum_comp e.symm (fun p => (kronecker (F p.1) (G p.2))ᴴ * kronecker (F p.1) (G p.2))
  · intro ρ
    unfold x8L QAlgorithms.krausApply
    rw [← Fintype.sum_prod_type']
    exact (Equiv.sum_comp e.symm (fun p => kronecker (F p.1) (G p.2) * ρ * (kronecker (F p.1) (G p.2))ᴴ)).symm

theorem x8_tc (U : Matrix C A ℂ) (V : Matrix E B ℂ) (X : Matrix (A × B) (A × B) ℂ) :
    QAlgorithms.Papers.Independent.Information100.P62.tensorChannel (QAlgorithms.conjSuperop U)
      (QAlgorithms.conjSuperop V) X = x8L (fun _ : Unit => U) (fun _ : Unit => V) X := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp only [QAlgorithms.Papers.Independent.Information100.P62.tensorChannel, x8L,
    QAlgorithms.conjSuperop, Finset.univ_unique, Finset.sum_singleton, Matrix.mul_apply,
    conjTranspose_apply, Matrix.kronecker, kroneckerMap_apply, Fintype.sum_prod_type, Matrix.single_apply,
    ite_and, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero, Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => arg 2; ext; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext; arg 2; ext; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext; arg 2; ext; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [star_mul']
  ring


def x8R (U : Matrix C A ℂ) (a0 : A) : Option C → Matrix A C ℂ
  | none => Uᴴ
  | some c => Matrix.single a0 c (1 : ℂ) * (1 - U * Uᴴ)

theorem x8_sum_single : ∑ c : C, (Matrix.single c c (1 : ℂ)) = 1 := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.single_apply, one_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

theorem x8_R_kraus (U : Matrix C A ℂ) (hU : Uᴴ * U = 1) (a0 : A) :
    ∑ o, (x8R U a0 o)ᴴ * x8R U a0 o = 1 := by
  rw [Fintype.sum_option]
  simp only [x8R, conjTranspose_conjTranspose, conjTranspose_mul, conjTranspose_single, star_one]
  have hP : (U * Uᴴ) * (U * Uᴴ) = U * Uᴴ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU, Matrix.one_mul]
  have hH : (1 - U * Uᴴ)ᴴ = 1 - U * Uᴴ := by
    rw [conjTranspose_sub, conjTranspose_one, conjTranspose_mul, conjTranspose_conjTranspose]
  have : ∀ c : C, (1 - U * Uᴴ)ᴴ * Matrix.single c a0 (1 : ℂ) * (Matrix.single a0 c (1 : ℂ) * (1 - U * Uᴴ)) =
      (1 - U * Uᴴ) * Matrix.single c c 1 * (1 - U * Uᴴ) := by
    intro c
    rw [hH, ← Matrix.mul_assoc, Matrix.mul_assoc _ (Matrix.single c a0 1), single_mul_single_same, mul_one]
  simp_rw [this, ← Finset.sum_mul, ← Finset.mul_sum, x8_sum_single, Matrix.mul_one, Matrix.sub_mul,
    Matrix.mul_sub, hP, Matrix.one_mul, Matrix.mul_one]
  abel

theorem x8_R_U (U : Matrix C A ℂ) (hU : Uᴴ * U = 1) (a0 : A) (c : C) : x8R U a0 (some c) * U = 0 := by
  simp only [x8R]
  rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hU, Matrix.mul_one, sub_self,
    Matrix.mul_zero]

theorem x8_kk (M : Matrix A C ℂ) (N : Matrix B E ℂ) (U : Matrix C A ℂ) (V : Matrix E B ℂ)
    (X : Matrix (A × B) (A × B) ℂ) :
    kronecker M N * (kronecker U V * X * (kronecker U V)ᴴ) * (kronecker M N)ᴴ =
      kronecker (M * U) (N * V) * X * (kronecker (M * U) (N * V))ᴴ := by
  simp only [Matrix.kronecker]
  rw [conjTranspose_kronecker, conjTranspose_kronecker, conjTranspose_kronecker, conjTranspose_mul,
    conjTranspose_mul, mul_kronecker_mul, mul_kronecker_mul]
  simp only [Matrix.mul_assoc]

theorem x8_recover (U : Matrix C A ℂ) (V : Matrix E B ℂ) (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1)
    (a0 : A) (b0 : B) (X : Matrix (A × B) (A × B) ℂ) :
    x8L (x8R U a0) (x8R V b0) (x8L (fun _ : Unit => U) (fun _ : Unit => V) X) = X := by
  unfold x8L
  simp only [Finset.univ_unique, Finset.sum_singleton, x8_kk, Fintype.sum_option, x8_R_U U hU,
    x8_R_U V hV]
  simp only [x8R, hU, hV, Matrix.kronecker, zero_kronecker, kronecker_zero, Matrix.zero_mul,
    Matrix.mul_zero, Finset.sum_const_zero, add_zero, one_kronecker_one, Matrix.one_mul,
    conjTranspose_one, Matrix.mul_one]

end QAlgorithms.Papers.Independent.Dependency50.P18

end

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P18

open scoped BigOperators ComplexOrder
open Matrix

attribute [local instance] Classical.propDecidable

variable {A B C E X : Type}
  [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Fintype X]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq E] [DecidableEq X]
  [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty E] [Nonempty X]

/-- Corollary 3, PDF pp.2–3, (10)–(11). The printed common PSD domain is corrected:
Gamma requires a state by (4) and the proof. Rectangular isometries can enlarge dimensions. -/
theorem x8_main (D : Divergence) (hD : IsGeneralizedDivergence D)
    (U : Matrix C A ℂ) (V : Matrix E B ℂ) (hU : Matrix.conjTranspose U * U = 1) (hV : Matrix.conjTranspose V * V = 1) :
    (∀ sigma : Matrix (A × B) (A × B) ℂ, sigma.PosSemidef →
      cGamma sigma = cGamma (QAlgorithms.Papers.Independent.Information100.P62.tensorChannel (QAlgorithms.conjSuperop U)
        (QAlgorithms.conjSuperop V) sigma)) ∧
    (∀ rho : Matrix (A × B) (A × B) ℂ, QAlgorithms.IsDensityMatrix rho →
      capitalGamma D rho = capitalGamma D (QAlgorithms.Papers.Independent.Information100.P62.tensorChannel (QAlgorithms.conjSuperop U)
        (QAlgorithms.conjSuperop V) rho)) := by
  have a0 : A := Classical.arbitrary A
  have b0 : B := Classical.arbitrary B
  have h1 : ∑ _i : Unit, (U)ᴴ * U = 1 := by simp [hU]
  have h2 : ∑ _i : Unit, (V)ᴴ * V = 1 := by simp [hV]
  have hT : QAlgorithms.Papers.Independent.Information100.P62.tensorChannel (QAlgorithms.conjSuperop U)
      (QAlgorithms.conjSuperop V) = x8L (fun _ : Unit => U) (fun _ : Unit => V) := funext (x8_tc U V)
  rw [hT]
  refine ⟨fun σ _ => ?_, fun ρ hρ => ?_⟩
  · unfold cGamma
    congr 1
    apply le_antisymm
    · conv_lhs => rw [← x8_recover U V hU hV a0 b0 σ]
      exact x8_mono _ _ (x8_R_kraus U hU a0) (x8_R_kraus V hV b0) _
    · exact x8_mono _ _ h1 h2 σ
  · have chW := x8_L_channel (fun _ : Unit => U) (fun _ : Unit => V) h1 h2
    have chR := x8_L_channel (x8R U a0) (x8R V b0) (x8_R_kraus U hU a0) (x8_R_kraus V hV b0)
    have hρ' : QAlgorithms.IsDensityMatrix (x8L (fun _ : Unit => U) (fun _ : Unit => V) ρ) :=
      ⟨x8_L_psd _ _ _ hρ.1, by rw [x8_L_trace _ _ h1 h2]; exact hρ.2⟩
    apply le_antisymm
    · unfold capitalGamma
      refine le_sInf ?_
      rintro r ⟨σ', hσ', hγ, rfl⟩
      refine sInf_le_of_le ⟨x8L (x8R U a0) (x8R V b0) σ', x8_L_psd _ _ _ hσ',
        (x8_mono _ _ (x8_R_kraus U hU a0) (x8_R_kraus V hV b0) σ').trans hγ, rfl⟩ ?_
      have := hD.dataProcessing _ σ' _ hρ' hσ' chR
      rwa [x8_recover U V hU hV a0 b0] at this
    · unfold capitalGamma
      refine le_sInf ?_
      rintro r ⟨σ, hσ, hγ, rfl⟩
      refine sInf_le_of_le ⟨x8L (fun _ : Unit => U) (fun _ : Unit => V) σ, x8_L_psd _ _ _ hσ,
        (x8_mono _ _ h1 h2 σ).trans hγ, rfl⟩ ?_
      exact hD.dataProcessing ρ σ _ hρ hσ chW

end QAlgorithms.Papers.Independent.Dependency50.P18

open scoped BigOperators ComplexOrder

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Dependency50.P18 in
theorem solution {A B C E : Type}
  [Fintype A] [Fintype B] [Fintype C] [Fintype E]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq E]
  [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty E]
 (D : Divergence) (hD : IsGeneralizedDivergence D)
    (U : Matrix C A ℂ) (V : Matrix E B ℂ) (hU : Matrix.conjTranspose U * U = 1) (hV : Matrix.conjTranspose V * V = 1) :
    (∀ sigma : Matrix (A × B) (A × B) ℂ, sigma.PosSemidef →
      cGamma sigma = cGamma (QAlgorithms.Papers.Independent.Information100.P62.tensorChannel (QAlgorithms.conjSuperop U)
        (QAlgorithms.conjSuperop V) sigma)) ∧
    (∀ rho : Matrix (A × B) (A × B) ℂ, QAlgorithms.IsDensityMatrix rho →
      capitalGamma D rho = capitalGamma D (QAlgorithms.Papers.Independent.Information100.P62.tensorChannel (QAlgorithms.conjSuperop U)
        (QAlgorithms.conjSuperop V) rho)) :=
  x8_main D hD U V hU hV
