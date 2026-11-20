-- Prove2me | solution 1 for SignRankMargin.OREquality.lemma_11
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:53:52.261591+00:00
-- url     : https://prove2.me/submissions/7bf4ef5b-4459-48bf-9f2b-ae70d6fdc49c

import Mathlib
import Definitions.Def_SignRankMargin_OREquality_Geometry

section
open Matrix Finset

namespace SignRankMargin.OREquality.Dev.L11

variable {X : Type*} [Fintype X] {r : ℕ}

/-- `∑ a_x w_x w_xᵀ`. -/
noncomputable def wsum (w : X → Fin r → ℝ) (a : X → ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  ∑ x, a x • vecMulVec (w x) (w x)

lemma wsum_qform (w : X → Fin r → ℝ) (a : X → ℝ) (v : Fin r → ℝ) :
    v ⬝ᵥ (wsum w a *ᵥ v) = ∑ x, a x * (w x ⬝ᵥ v) ^ 2 := by
  simp [wsum, Matrix.sum_mulVec, dotProduct_sum, Matrix.smul_mulVec, vecMulVec_mulVec,
    dotProduct_smul, pow_two, mul_assoc, dotProduct_comm]

lemma wsum_isHermitian (w : X → Fin r → ℝ) (a : X → ℝ) : (wsum w a).IsHermitian := by
  ext i j
  simp [wsum, Matrix.conjTranspose_apply, Matrix.sum_apply, vecMulVec_apply, mul_comm]

lemma det_add_rank_one {A : Matrix (Fin r) (Fin r) ℝ} (hA : IsUnit A.det) (c : ℝ)
    (w : Fin r → ℝ) :
    (A + c • vecMulVec w w).det = A.det * (1 + c * (w ⬝ᵥ (A⁻¹ *ᵥ w))) := by
  have h : c • vecMulVec w w = replicateCol Unit (c • w) * replicateRow Unit w := by
    ext i j
    simp [vecMulVec_apply, Matrix.mul_apply, mul_assoc]
  rw [h, Matrix.det_add_replicateCol_mul_replicateRow hA]
  congr 1
  rw [Matrix.det_unique]
  simp only [Pi.add_apply, Matrix.one_apply_eq, Matrix.mul_apply, replicateRow_apply,
    replicateCol_apply, Pi.smul_apply, smul_eq_mul, Finset.univ_unique, Finset.sum_singleton,
    Matrix.add_apply]
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- The vectors span. -/
def Spans (w : X → Fin r → ℝ) : Prop := ∀ v : Fin r → ℝ, (∀ x, w x ⬝ᵥ v = 0) → v = 0

lemma wsum_posDef {w : X → Fin r → ℝ} {a : X → ℝ} (ha : ∀ x, 0 < a x) (hs : Spans w) :
    (wsum w a).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨wsum_isHermitian w a, fun v hv => ?_⟩
  have hv' : ¬ ∀ x, w x ⬝ᵥ v = 0 := fun h => hv (hs v h)
  push Not at hv'
  obtain ⟨x0, hx0⟩ := hv'
  have : star v = v := by simp
  rw [this, wsum_qform]
  exact Finset.sum_pos' (fun x _ => mul_nonneg (ha x).le (sq_nonneg _))
    ⟨x0, Finset.mem_univ _, mul_pos (ha x0) (by positivity)⟩

lemma det_add_sum_ge [DecidableEq X] {A : Matrix (Fin r) (Fin r) ℝ} (hA : A.PosDef)
    (w : X → Fin r → ℝ) (c : X → ℝ) (s : Finset X) (hc : ∀ x ∈ s, 0 ≤ c x) :
    (A + ∑ x ∈ s, c x • vecMulVec (w x) (w x)).PosDef ∧
      A.det ≤ (A + ∑ x ∈ s, c x • vecMulVec (w x) (w x)).det := by
  induction s using Finset.induction_on with
  | empty => simpa using hA
  | insert y s hy ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun x hx => hc x (Finset.mem_insert_of_mem hx))
    have hcy := hc y (Finset.mem_insert_self _ _)
    have hsum : A + ∑ x ∈ insert y s, c x • vecMulVec (w x) (w x)
        = (A + ∑ x ∈ s, c x • vecMulVec (w x) (w x)) + c y • vecMulVec (w y) (w y) := by
      rw [Finset.sum_insert hy]; abel
    rw [hsum]
    set A' := A + ∑ x ∈ s, c x • vecMulVec (w x) (w x) with hA'
    have hdet : IsUnit A'.det := (isUnit_iff_ne_zero).2 ih1.det_pos.ne'
    have hsemi : (c y • vecMulVec (w y) (w y)).PosSemidef := by
      refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun v => ?_
      · ext i j; simp [Matrix.conjTranspose_apply, vecMulVec_apply, mul_comm, mul_left_comm]
      · have : star v = v := by simp
        rw [this]
        simp [Matrix.smul_mulVec, vecMulVec_mulVec, dotProduct_smul, pow_two, dotProduct_comm]
        exact mul_nonneg hcy (mul_self_nonneg _)
    refine ⟨ih1.add_posSemidef hsemi, ?_⟩
    rw [det_add_rank_one hdet]
    have hinv : (A'⁻¹).PosDef := Matrix.posDef_inv_iff.2 ih1
    have h0 : 0 ≤ w y ⬝ᵥ (A'⁻¹ *ᵥ w y) := by
      have := hinv.posSemidef.dotProduct_mulVec_nonneg (w y)
      simpa using this
    have hpos := ih1.det_pos
    calc A.det ≤ A'.det := ih2
      _ ≤ A'.det * (1 + c y * (w y ⬝ᵥ (A'⁻¹ *ᵥ w y))) := by
        have : 0 ≤ c y * (w y ⬝ᵥ (A'⁻¹ *ᵥ w y)) := mul_nonneg hcy h0
        nlinarith

/-- General position: every `r` of the vectors are linearly independent. -/
def GenPos (w : X → Fin r → ℝ) : Prop :=
  ∀ f : Fin r → X, Function.Injective f → (Matrix.of fun i j => w (f i) j).det ≠ 0

lemma spans_of_det {w : X → Fin r → ℝ} (f : Fin r → X)
    (hf : (Matrix.of fun i j => w (f i) j).det ≠ 0) : Spans w := by
  intro v hv
  apply Matrix.eq_zero_of_mulVec_eq_zero hf
  ext i
  simpa [Matrix.mulVec, dotProduct] using hv (f i)

lemma wsum_comp_eq (w : X → Fin r → ℝ) (a : X → ℝ) (f : Fin r → X) :
    wsum (fun i => w (f i)) (fun i => a (f i)) =
      (Matrix.of fun i j => w (f i) j)ᵀ * Matrix.diagonal (fun i => a (f i)) *
        (Matrix.of fun i j => w (f i) j) := by
  ext j k
  simp [wsum, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.sum_apply, vecMulVec_apply]
  exact Finset.sum_congr rfl fun _ _ => by ring

lemma det_wsum_ge [DecidableEq X] {w : X → Fin r → ℝ} {a : X → ℝ} (ha : ∀ x, 0 < a x)
    (f : Fin r → X) (hf : Function.Injective f)
    (hdet : (Matrix.of fun i j => w (f i) j).det ≠ 0) :
    (∏ i, a (f i)) * (Matrix.of fun i j => w (f i) j).det ^ 2 ≤ (wsum w a).det := by
  classical
  have hs : Spans (fun i => w (f i)) := by
    have : Spans w := spans_of_det f hdet
    intro v hv
    exact (spans_of_det (w := fun i : Fin r => w (f i)) id hdet) v hv
  have hA : (wsum (fun i => w (f i)) (fun i => a (f i))).PosDef :=
    wsum_posDef (fun i => ha _) hs
  have hsplit : wsum w a = wsum (fun i => w (f i)) (fun i => a (f i)) +
      ∑ x ∈ (Finset.univ.image f)ᶜ, a x • vecMulVec (w x) (w x) := by
    unfold wsum
    rw [← Finset.sum_add_sum_compl (Finset.univ.image f), Finset.sum_image (fun i _ j _ h => hf h)]
  have := (det_add_sum_ge hA w a (Finset.univ.image f)ᶜ (fun x _ => (ha x).le)).2
  rw [hsplit]
  refine le_trans (le_of_eq ?_) this
  rw [wsum_comp_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  ring

omit [Fintype X] in
lemma card_compl_erase [Fintype X] [DecidableEq X] (I : Finset X) (y : X) (hy : y ∈ Iᶜ) :
    ((Iᶜ).erase y).card + 1 = Fintype.card X - I.card := by
  rw [Finset.card_erase_of_mem hy, Finset.card_compl]
  have : 0 < (Iᶜ).card := Finset.card_pos.2 ⟨y, hy⟩
  rw [Finset.card_compl] at this
  omega

lemma exists_subset_sum_ge [DecidableEq X] (b : X → ℝ) (hb : ∑ x, b x = 0) (hr1 : 1 ≤ r)
    (hrM : r < Fintype.card X) :
    ∃ I : Finset X, I.card = r ∧ ∀ z, |b z| ≤ (Fintype.card X : ℝ) ^ 2 * ∑ x ∈ I, b x := by
  have hne : (Finset.powersetCard r (Finset.univ : Finset X)).Nonempty := by
    rw [Finset.powersetCard_nonempty]; simpa using hrM.le
  obtain ⟨I, hI, hmax⟩ := Finset.exists_max_image _ (fun I => ∑ x ∈ I, b x) hne
  rw [Finset.mem_powersetCard] at hI
  have hIc : I.card = r := hI.2
  refine ⟨I, hIc, ?_⟩
  have hswap : ∀ x ∈ I, ∀ y ∉ I, b y ≤ b x := by
    intro x hx y hy
    have hy' : y ∉ I.erase x := fun h => hy (Finset.mem_of_mem_erase h)
    have h1 := hmax (insert y (I.erase x)) (by
      rw [Finset.mem_powersetCard]
      refine ⟨Finset.subset_univ _, ?_⟩
      rw [Finset.card_insert_of_notMem hy', Finset.card_erase_of_mem hx]
      omega)
    rw [Finset.sum_insert hy'] at h1
    have h2 := Finset.add_sum_erase I b hx
    linarith
  have hInon : I.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨x0, hx0, hm⟩ := Finset.exists_min_image I b hInon
  set m := b x0 with hmdef
  set t := ∑ x ∈ I, b x with htdef
  have hrm : (r : ℝ) * m ≤ t := by
    have := Finset.card_nsmul_le_sum I b m hm
    simpa [hIc] using this
  have hcomp : ∑ x ∈ Iᶜ, b x = -t := by
    have := Finset.sum_compl_add_sum I b
    linarith
  have hcm : ∀ y ∈ Iᶜ, b y ≤ m := fun y hy =>
    hswap x0 hx0 y (Finset.mem_compl.1 hy)
  have hcardc : ((Iᶜ).card : ℝ) = (Fintype.card X : ℝ) - r := by
    rw [Finset.card_compl, hIc]
    have : r ≤ Fintype.card X := hrM.le
    push_cast [this]; ring
  have hup : ∑ x ∈ Iᶜ, b x ≤ ((Fintype.card X : ℝ) - r) * m := by
    have := Finset.sum_le_card_nsmul Iᶜ b m hcm
    simpa [hcardc] using this
  have hr1' : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hrM' : (r : ℝ) + 1 ≤ Fintype.card X := by exact_mod_cast hrM
  have ht0 : 0 ≤ t := by nlinarith
  have hmt : m ≤ t := by
    rcases le_or_gt 0 m with h | h
    · nlinarith
    · linarith
  have hM1 : (1 : ℝ) ≤ Fintype.card X := by linarith
  set M : ℝ := (Fintype.card X : ℝ) with hMdef
  -- lower bound for elements outside I
  have hlow_c : ∀ y ∈ Iᶜ, -(M - r) * t ≤ b y := by
    intro y hy
    have h1 := Finset.add_sum_erase Iᶜ b hy
    have h2 : ∑ x ∈ (Iᶜ).erase y, b x ≤ (((Iᶜ).erase y).card : ℝ) * m := by
      have := Finset.sum_le_card_nsmul ((Iᶜ).erase y) b m
        (fun x hx => hcm x (Finset.mem_of_mem_erase hx))
      simpa using this
    have h3 := card_compl_erase I y hy
    have h4 : (((Iᶜ).erase y).card : ℝ) = M - r - 1 := by
      have : ((Iᶜ).erase y).card = Fintype.card X - I.card - 1 := by omega
      rw [this, hIc]
      have : 1 ≤ Fintype.card X - r := by omega
      push_cast [this, hrM.le]; ring
    rw [h4] at h2
    have h5 : 0 ≤ M - r - 1 := by linarith
    nlinarith
  have hlow : ∀ z, -(M * t) ≤ b z := by
    intro z
    by_cases hz : z ∈ I
    · have hy : (Iᶜ).Nonempty := Finset.card_pos.1 (by rw [Finset.card_compl]; omega)
      obtain ⟨y, hy⟩ := hy
      have := hlow_c y hy
      have := hswap z hz y (Finset.mem_compl.1 hy)
      nlinarith
    · have := hlow_c z (Finset.mem_compl.2 hz)
      nlinarith
  intro z
  have hM2 : M ≤ M ^ 2 := by nlinarith
  rw [abs_le]
  constructor
  · nlinarith [hlow z, mul_le_mul_of_nonneg_right hM2 ht0]
  · by_cases hz : z ∈ I
    · have h1 := Finset.add_sum_erase I b hz
      have h2 : ∑ x ∈ I.erase z, b x ≥ ((I.erase z).card : ℝ) * (-(M * t)) := by
        have := Finset.card_nsmul_le_sum (I.erase z) b (-(M * t))
          (fun x _ => hlow x)
        simpa using this
      have h3 : ((I.erase z).card : ℝ) = r - 1 := by
        rw [Finset.card_erase_of_mem hz, hIc]
        push_cast [hr1]; ring
      rw [h3] at h2
      have h7 : b z ≤ t + ((r : ℝ) - 1) * (M * t) := by nlinarith
      have h8 : ((r : ℝ) - 1) * (M * t) ≤ (M - 1) * (M * t) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      nlinarith [mul_nonneg ht0 (sub_nonneg.2 hM1)]
    · have := hcm z (Finset.mem_compl.2 hz)
      nlinarith

lemma wsum_update [DecidableEq X] (w : X → Fin r → ℝ) (a : X → ℝ) (x0 : X) (t : ℝ) :
    wsum w (Function.update a x0 t) =
      wsum w a + (t - a x0) • vecMulVec (w x0) (w x0) := by
  unfold wsum
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x0),
    ← Finset.add_sum_erase _ (fun x => a x • vecMulVec (w x) (w x)) (Finset.mem_univ x0)]
  have : ∀ y ∈ Finset.univ.erase x0,
      Function.update a x0 t y • vecMulVec (w y) (w y) = a y • vecMulVec (w y) (w y) :=
    fun y hy => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hy)]
  rw [Finset.sum_congr rfl this]
  simp only [Function.update_self, sub_smul]
  abel

/-- The dual potential. -/
noncomputable def Psi (w : X → Fin r → ℝ) (b : X → ℝ) : ℝ :=
  Real.log (wsum w (fun x => Real.exp (b x))).det - ((r : ℝ) / Fintype.card X) * ∑ x, b x

lemma wsum_exp_posDef {w : X → Fin r → ℝ} (hs : Spans w) (b : X → ℝ) :
    (wsum w (fun x => Real.exp (b x))).PosDef :=
  wsum_posDef (fun x => Real.exp_pos _) hs

lemma psi_update [DecidableEq X] {w : X → Fin r → ℝ} (hs : Spans w) (b : X → ℝ) (x0 : X)
    (s : ℝ) :
    Psi w (Function.update b x0 (b x0 + s)) = Psi w b +
      (Real.log (1 + (Real.exp s - 1) * (Real.exp (b x0) *
        (w x0 ⬝ᵥ ((wsum w (fun x => Real.exp (b x)))⁻¹ *ᵥ w x0)))) -
        ((r : ℝ) / Fintype.card X) * s) := by
  set B := wsum w (fun x => Real.exp (b x)) with hB
  set ℓ := Real.exp (b x0) * (w x0 ⬝ᵥ (B⁻¹ *ᵥ w x0)) with hℓ
  have hexp : (fun x => Real.exp (Function.update b x0 (b x0 + s) x)) =
      Function.update (fun x => Real.exp (b x)) x0 (Real.exp (b x0) * Real.exp s) := by
    ext x
    by_cases hx : x = x0
    · subst hx; simp [Real.exp_add]
    · simp [Function.update_of_ne hx]
  have hBpos := wsum_exp_posDef hs b
  have hBpos' := wsum_exp_posDef hs (Function.update b x0 (b x0 + s))
  have hdetB : IsUnit B.det := (isUnit_iff_ne_zero).2 hBpos.det_pos.ne'
  have hdet : (wsum w (fun x => Real.exp (Function.update b x0 (b x0 + s) x))).det =
      B.det * (1 + (Real.exp s - 1) * ℓ) := by
    rw [hexp, wsum_update, ← hB, det_add_rank_one hdetB]
    congr 1
    simp only [hℓ]
    ring
  have hY : 0 < 1 + (Real.exp s - 1) * ℓ := by
    have h1 := hBpos'.det_pos
    rw [hdet] at h1
    exact pos_of_mul_pos_right h1 hBpos.det_pos.le |>.trans_eq rfl
  unfold Psi
  rw [hdet, Real.log_mul hBpos.det_pos.ne' hY.ne']
  have hsum : ∑ x, Function.update b x0 (b x0 + s) x = ∑ x, b x + s := by
    rw [Finset.sum_update_of_mem (Finset.mem_univ x0)]
    have := Finset.add_sum_erase Finset.univ b (Finset.mem_univ x0)
    rw [Finset.sdiff_singleton_eq_erase]
    linarith
  rw [hsum]
  ring

lemma eq_of_forall_log_nonneg (ℓ p : ℝ)
    (h : ∀ s : ℝ, 0 ≤ Real.log (1 + (Real.exp s - 1) * ℓ) - p * s) : ℓ = p := by
  have hd : HasDerivAt (fun s : ℝ => Real.log (1 + (Real.exp s - 1) * ℓ) - p * s)
      (ℓ - p) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => 1 + (Real.exp s - 1) * ℓ) ℓ 0 := by
      have := (((Real.hasDerivAt_exp 0).sub_const 1).mul_const ℓ).const_add 1
      simpa using this
    have h2 : HasDerivAt (fun s : ℝ => Real.log (1 + (Real.exp s - 1) * ℓ) - p * s)
        (ℓ / (1 + (Real.exp 0 - 1) * ℓ) - p * 1) 0 :=
      (h1.log (by simp)).sub ((hasDerivAt_id (0 : ℝ)).const_mul p)
    simpa using h2
  have hmin : IsLocalMin (fun s : ℝ => Real.log (1 + (Real.exp s - 1) * ℓ) - p * s) 0 := by
    refine Filter.Eventually.of_forall fun s => ?_
    have := h s
    simpa using this
  have := hmin.hasDerivAt_eq_zero hd
  linarith

lemma leverage_of_min [DecidableEq X] {w : X → Fin r → ℝ} (hs : Spans w) (b0 : X → ℝ)
    (hmin : ∀ b, Psi w b0 ≤ Psi w b) (x0 : X) :
    Real.exp (b0 x0) * (w x0 ⬝ᵥ ((wsum w (fun x => Real.exp (b0 x)))⁻¹ *ᵥ w x0)) =
      (r : ℝ) / Fintype.card X := by
  apply eq_of_forall_log_nonneg
  intro s
  have h1 := hmin (Function.update b0 x0 (b0 x0 + s))
  rw [psi_update hs] at h1
  linarith

lemma psi_continuous {w : X → Fin r → ℝ} (hs : Spans w) : Continuous (Psi w) := by
  have h1 : Continuous fun b : X → ℝ => wsum w (fun x => Real.exp (b x)) := by
    unfold wsum
    refine continuous_finsetSum _ fun x _ => ?_
    exact ((Real.continuous_exp.comp (continuous_apply x))).smul continuous_const
  have h2 : Continuous fun b : X → ℝ => (wsum w (fun x => Real.exp (b x))).det :=
    h1.matrix_det
  unfold Psi
  refine Continuous.sub (h2.log fun b => (wsum_exp_posDef hs b).det_pos.ne') ?_
  exact continuous_const.mul (continuous_finsetSum _ fun x _ => continuous_apply x)

lemma psi_shift {w : X → Fin r → ℝ} (hs : Spans w) (hX : Nonempty X) (b : X → ℝ) (c : ℝ) :
    Psi w (fun x => b x - c) = Psi w b := by
  have h1 : wsum w (fun x => Real.exp (b x - c)) =
      Real.exp (-c) • wsum w (fun x => Real.exp (b x)) := by
    unfold wsum
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [smul_smul, sub_eq_add_neg, Real.exp_add, mul_comm]
  have hpos := (wsum_exp_posDef hs b).det_pos
  have hM : (Fintype.card X : ℝ) ≠ 0 := by
    have : 0 < Fintype.card X := Fintype.card_pos
    positivity
  unfold Psi
  rw [h1, Matrix.det_smul, Real.log_mul (by positivity) hpos.ne']
  simp only [Fintype.card_fin, Real.log_pow, Real.log_exp, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

lemma exists_inj_image [DecidableEq X] (I : Finset X) (hI : I.card = r) :
    ∃ f : Fin r → X, Function.Injective f ∧ Finset.univ.image f = I := by
  let e : Fin r ≃ I := (I.equivFinOfCardEq hI).symm
  refine ⟨fun i => (e i : X), Subtype.val_injective.comp e.injective, ?_⟩
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩; exact (e i).2
  · intro hx; exact ⟨e.symm ⟨x, hx⟩, by simp⟩

lemma exists_delta [DecidableEq X] {w : X → Fin r → ℝ} (hgp : GenPos w)
    (hrM : r ≤ Fintype.card X) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f : Fin r → X, Function.Injective f →
      δ ≤ (Matrix.of fun i j => w (f i) j).det ^ 2 := by
  classical
  have hne : ((Finset.univ : Finset (Fin r → X)).filter Function.Injective).Nonempty := by
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := Fin r) (β := X) (by simpa using hrM)
    exact ⟨e, by simp [e.injective]⟩
  obtain ⟨f0, hf0, hmin⟩ := Finset.exists_min_image _
    (fun f : Fin r → X => (Matrix.of fun i j => w (f i) j).det ^ 2) hne
  rw [Finset.mem_filter] at hf0
  refine ⟨_, by have := hgp f0 hf0.2; positivity, fun f hf => hmin f (by simp [hf])⟩

lemma psi_ge [DecidableEq X] {w : X → Fin r → ℝ} (hgp : GenPos w) (hr1 : 1 ≤ r)
    (hrM : r < Fintype.card X) :
    ∃ L : ℝ, ∀ b : X → ℝ, ∑ x, b x = 0 → ∀ z,
      L + |b z| / (Fintype.card X : ℝ) ^ 2 ≤ Psi w b := by
  obtain ⟨δ, hδ, hδf⟩ := exists_delta hgp hrM.le
  refine ⟨Real.log δ, fun b hb z => ?_⟩
  obtain ⟨I, hIc, hI⟩ := exists_subset_sum_ge b hb hr1 hrM
  obtain ⟨f, hf, hfI⟩ := exists_inj_image I hIc
  have hs : Spans w := spans_of_det f (hgp f hf)
  have hdet := det_wsum_ge (w := w) (a := fun x => Real.exp (b x)) (fun x => Real.exp_pos _) f hf
    (hgp f hf)
  have hprod : ∏ i, Real.exp (b (f i)) = Real.exp (∑ x ∈ I, b x) := by
    rw [← Real.exp_sum, ← hfI, Finset.sum_image (fun i _ j _ h => hf h)]
  rw [hprod] at hdet
  have h1 : Real.exp (∑ x ∈ I, b x) * δ ≤ (wsum w (fun x => Real.exp (b x))).det :=
    le_trans (mul_le_mul_of_nonneg_left (hδf f hf) (Real.exp_pos _).le) hdet
  have h2 : (∑ x ∈ I, b x) + Real.log δ ≤
      Real.log (wsum w (fun x => Real.exp (b x))).det := by
    rw [← Real.log_exp (∑ x ∈ I, b x), ← Real.log_mul (Real.exp_pos _).ne' hδ.ne']
    exact Real.log_le_log (by positivity) h1
  have hM : (0 : ℝ) < (Fintype.card X : ℝ) ^ 2 := by
    have : 0 < Fintype.card X := by omega
    positivity
  have h3 : |b z| / (Fintype.card X : ℝ) ^ 2 ≤ ∑ x ∈ I, b x := by
    rw [div_le_iff₀ hM]; linarith [hI z]
  unfold Psi
  rw [hb]
  linarith

lemma exists_psi_min [DecidableEq X] {w : X → Fin r → ℝ} (hgp : GenPos w) (hr1 : 1 ≤ r)
    (hrM : r < Fintype.card X) : ∃ b0 : X → ℝ, ∀ b, Psi w b0 ≤ Psi w b := by
  have hX : Nonempty X := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨f, hf⟩ : ∃ f : Fin r → X, Function.Injective f := by
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := Fin r) (β := X)
      (by simpa using hrM.le)
    exact ⟨e, e.injective⟩
  have hs : Spans w := spans_of_det f (hgp f hf)
  obtain ⟨L, hL⟩ := psi_ge hgp hr1 hrM
  set M : ℝ := (Fintype.card X : ℝ) with hM
  have hM0 : 0 < M := by
    have : 0 < Fintype.card X := by omega
    positivity
  set R : ℝ := M ^ 2 * (|Psi w 0 - L| + 1) with hR
  have hR0 : 0 ≤ R := by positivity
  set K : Set (X → ℝ) := Metric.closedBall 0 R ∩ {b | ∑ x, b x = 0} with hK
  have hKc : IsCompact K :=
    (isCompact_closedBall 0 R).inter_right
      (isClosed_eq (continuous_finsetSum _ fun x _ => continuous_apply x) continuous_const)
  have hK0 : (0 : X → ℝ) ∈ K := by simp [hK, hR0]
  obtain ⟨b1, hb1, hmin⟩ := hKc.exists_isMinOn ⟨0, hK0⟩ (psi_continuous hs).continuousOn
  refine ⟨b1, fun b => ?_⟩
  set c : ℝ := (∑ x, b x) / M with hc
  set b' : X → ℝ := fun x => b x - c with hb'
  have hsum : ∑ x, b' x = 0 := by
    simp only [hb', Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]
    field_simp
    ring
  have hPb : Psi w b' = Psi w b := psi_shift hs hX b c
  rw [← hPb]
  by_cases hbig : ‖b'‖ ≤ R
  · exact hmin (show b' ∈ K from ⟨by simpa using hbig, hsum⟩)
  · push Not at hbig
    obtain ⟨z, hz⟩ : ∃ z, R < |b' z| := by
      by_contra hcon
      push Not at hcon
      exact absurd ((pi_norm_le_iff_of_nonneg hR0).2 fun z => by simpa using hcon z) (not_le.2 hbig)
    have h1 := hL b' hsum z
    have h2 : |Psi w 0 - L| + 1 ≤ |b' z| / M ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have h3 : Psi w 0 ≤ Psi w b' := by
      have := le_abs_self (Psi w 0 - L)
      linarith
    exact le_trans (hmin hK0) h3

lemma leverage_square [DecidableEq X] {w : X → Fin r → ℝ} (hgp : GenPos w)
    (hrM : r = Fintype.card X) (x : X) :
    (1 : ℝ) * (w x ⬝ᵥ ((wsum w (fun _ => 1))⁻¹ *ᵥ w x)) = (r : ℝ) / Fintype.card X := by
  have hM : (Fintype.card X : ℝ) ≠ 0 := by
    have : x ∈ (Finset.univ : Finset X) := Finset.mem_univ x
    have : 0 < Fintype.card X := Fintype.card_pos_iff.2 ⟨x⟩
    positivity
  rw [← hrM] at hM ⊢
  rw [show (r : ℝ) / r = 1 from div_self (by simpa [hrM] using hM)]
  let e : Fin r ≃ X := Fintype.equivOfCardEq (by simpa using hrM)
  set W : Matrix (Fin r) (Fin r) ℝ := Matrix.of fun i j => w (e i) j with hW
  have hWdet : W.det ≠ 0 := hgp e e.injective
  have hB : wsum w (fun _ => (1 : ℝ)) = Wᵀ * W := by
    have h1 : wsum w (fun _ => (1 : ℝ)) = wsum (fun i => w (e i)) (fun _ => (1 : ℝ)) := by
      unfold wsum
      exact (Equiv.sum_comp e (fun x => (1 : ℝ) • vecMulVec (w x) (w x))).symm
    rw [h1]
    have := wsum_comp_eq w (fun _ => (1 : ℝ)) e
    simpa using this
  have hWu : IsUnit W.det := isUnit_iff_ne_zero.2 hWdet
  have hWtu : IsUnit Wᵀ.det := by simpa [Matrix.det_transpose] using hWu
  have hkey : W * (wsum w (fun _ => (1 : ℝ)))⁻¹ * Wᵀ = 1 := by
    rw [hB, Matrix.mul_inv_rev]
    calc W * (W⁻¹ * (Wᵀ)⁻¹) * Wᵀ = (W * W⁻¹) * ((Wᵀ)⁻¹ * Wᵀ) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.mul_nonsing_inv _ hWu, Matrix.nonsing_inv_mul _ hWtu, Matrix.mul_one]
  obtain ⟨i, rfl⟩ := e.surjective x
  have h1 := congrFun (congrFun hkey i) i
  have h2 : ((W * (wsum w (fun _ => (1 : ℝ)))⁻¹ * Wᵀ) i i) =
      w (e i) ⬝ᵥ ((wsum w (fun _ => (1 : ℝ)))⁻¹ *ᵥ w (e i)) := by
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, hW, Matrix.of_apply,
      Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [← h2, h1]
  simp

/-- Forster's theorem, dual (equal leverage score) form. -/
theorem forster_dual [DecidableEq X] {w : X → Fin r → ℝ} (hgp : GenPos w) (hr1 : 1 ≤ r)
    (hrM : r ≤ Fintype.card X) :
    ∃ a : X → ℝ, (∀ x, 0 < a x) ∧ ∀ x,
      a x * (w x ⬝ᵥ ((wsum w a)⁻¹ *ᵥ w x)) = (r : ℝ) / Fintype.card X := by
  rcases hrM.eq_or_lt with h | h
  · exact ⟨fun _ => 1, fun _ => one_pos, leverage_square hgp h⟩
  · obtain ⟨b0, hb0⟩ := exists_psi_min hgp hr1 h
    obtain ⟨f, hf⟩ : ∃ f : Fin r → X, Function.Injective f := by
      obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := Fin r) (β := X)
        (by simpa using hrM)
      exact ⟨e, e.injective⟩
    have hs : Spans w := spans_of_det f (hgp f hf)
    exact ⟨fun x => Real.exp (b0 x), fun x => Real.exp_pos _, leverage_of_min hs b0 hb0⟩

lemma exists_sqrt {B : Matrix (Fin r) (Fin r) ℝ} (hB : B.PosDef) :
    ∃ S : Matrix (Fin r) (Fin r) ℝ, Sᵀ = S ∧ S * S = B ∧ S.det ≠ 0 := by
  have hH := hB.1
  set U : Matrix (Fin r) (Fin r) ℝ := (hH.eigenvectorUnitary : Matrix (Fin r) (Fin r) ℝ) with hU
  have h2 : Uᵀ * U = 1 := by
    have h := Unitary.coe_star_mul_self hH.eigenvectorUnitary
    rwa [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hspec : B = U * Matrix.diagonal hH.eigenvalues * Uᵀ := by
    have := hH.spectral_theorem
    simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, hU] using this
  have hev : ∀ i, 0 ≤ hH.eigenvalues i := fun i => (hB.eigenvalues_pos i).le
  have hsq : (U * Matrix.diagonal (fun i => Real.sqrt (hH.eigenvalues i)) * Uᵀ) *
      (U * Matrix.diagonal (fun i => Real.sqrt (hH.eigenvalues i)) * Uᵀ) = B := by
    have hd : Matrix.diagonal (fun i => Real.sqrt (hH.eigenvalues i)) *
        Matrix.diagonal (fun i => Real.sqrt (hH.eigenvalues i)) =
        Matrix.diagonal hH.eigenvalues := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      ext i
      exact Real.mul_self_sqrt (hev i)
    calc U * Matrix.diagonal (fun i => Real.sqrt (hH.eigenvalues i)) * Uᵀ *
          (U * Matrix.diagonal (fun i => Real.sqrt (hH.eigenvalues i)) * Uᵀ)
        = U * (Matrix.diagonal (fun i => Real.sqrt (hH.eigenvalues i)) * (Uᵀ * U) *
            Matrix.diagonal (fun i => Real.sqrt (hH.eigenvalues i))) * Uᵀ := by
          simp only [Matrix.mul_assoc]
      _ = B := by rw [h2, Matrix.mul_one, hd]; exact hspec.symm
  refine ⟨U * Matrix.diagonal (fun i => Real.sqrt (hH.eigenvalues i)) * Uᵀ, ?_, hsq, ?_⟩
  · simp [Matrix.transpose_mul, Matrix.mul_assoc]
  · intro h0
    have : B.det = 0 := by
      rw [← hsq, Matrix.det_mul, h0]; simp
    exact hB.det_pos.ne' this

lemma ip_toLp (x y : Fin r → ℝ) :
    inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin r)) (WithLp.toLp 2 y) = x ⬝ᵥ y := by
  rw [EuclideanSpace.inner_toLp_toLp]
  simp [dotProduct_comm]

lemma sym_dot {S : Matrix (Fin r) (Fin r) ℝ} (hS : Sᵀ = S) (x y : Fin r → ℝ) :
    (S *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (S *ᵥ y) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hS]

lemma final_step {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y] [DecidableEq X]
    (F : Matrix X Y Bool) {r : ℕ} (w : X → Fin r → ℝ) (v : Y → Fin r → ℝ)
    (hgp : GenPos w) (hr1 : 1 ≤ r) (hrM : r ≤ Fintype.card X)
    (hF : StrictRealizes F (fun x y => w x ⬝ᵥ v y)) :
    ∃ (u : X → EuclideanSpace ℝ (Fin r)) (v' : Y → EuclideanSpace ℝ (Fin r)),
      UnitRealization F r u v' ∧
      uniformAverage (fun x y => |inner ℝ (u x) (v' y)| ^ 2) = 1 / (r : ℝ) := by
  obtain ⟨a, ha, hlev⟩ := forster_dual hgp hr1 hrM
  obtain ⟨f, hf⟩ : ∃ f : Fin r → X, Function.Injective f := by
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := Fin r) (β := X)
      (by simpa using hrM)
    exact ⟨e, e.injective⟩
  have hspan : Spans w := spans_of_det f (hgp f hf)
  have hBpos := wsum_posDef ha hspan
  set B := wsum w a with hB
  obtain ⟨S, hSt, hSS, hSdet⟩ := exists_sqrt hBpos
  have hSu : IsUnit S.det := isUnit_iff_ne_zero.2 hSdet
  set T := S⁻¹ with hT
  have hTt : Tᵀ = T := by rw [hT, Matrix.transpose_nonsing_inv, hSt]
  have hST : S * T = 1 := Matrix.mul_nonsing_inv S hSu
  have hTS : T * S = 1 := Matrix.nonsing_inv_mul S hSu
  have hBinv : B⁻¹ = T * T := by rw [← hSS, Matrix.mul_inv_rev]
  have hM : (0 : ℝ) < Fintype.card X := by
    have : 0 < Fintype.card X := Fintype.card_pos
    positivity
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr1
  -- nonvanishing of v
  have hvne : ∀ y, v y ≠ 0 := by
    intro y hy
    obtain ⟨x⟩ := ‹Nonempty X›
    have := hF x y
    simp only [hy, dotProduct_zero] at this
    split_ifs at this <;> exact lt_irrefl _ this
  set p : X → Fin r → ℝ := fun x => T *ᵥ w x with hp
  set q : Y → Fin r → ℝ := fun y => S *ᵥ v y with hq
  have hpq : ∀ x y, p x ⬝ᵥ q y = w x ⬝ᵥ v y := by
    intro x y
    simp only [hp, hq]
    rw [sym_dot hTt, Matrix.mulVec_mulVec, hTS, Matrix.one_mulVec]
  have hpp : ∀ x, p x ⬝ᵥ p x = w x ⬝ᵥ (B⁻¹ *ᵥ w x) := by
    intro x
    simp only [hp]
    rw [sym_dot hTt, Matrix.mulVec_mulVec, hBinv]
  have hlev' : ∀ x, p x ⬝ᵥ p x = (r : ℝ) / (Fintype.card X * a x) := by
    intro x
    rw [hpp]
    have := hlev x
    have hax := ha x
    field_simp
    field_simp at this
    linarith
  have hppos : ∀ x, 0 < p x ⬝ᵥ p x := fun x => by
    rw [hlev']; have := ha x; positivity
  have hqq : ∀ y, q y ⬝ᵥ q y = ∑ x, a x * (w x ⬝ᵥ v y) ^ 2 := by
    intro y
    simp only [hq]
    rw [sym_dot hSt, Matrix.mulVec_mulVec, hSS, ← wsum_qform]
  have hqpos : ∀ y, 0 < q y ⬝ᵥ q y := by
    intro y
    rw [hqq]
    obtain ⟨x0, hx0⟩ : ∃ x0, w x0 ⬝ᵥ v y ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hvne y (hspan _ (fun x => by simpa [dotProduct_comm] using hcon x))
    exact Finset.sum_pos' (fun x _ => mul_nonneg (ha x).le (sq_nonneg _))
      ⟨x0, Finset.mem_univ _, mul_pos (ha x0) (by positivity)⟩
  let P : X → EuclideanSpace ℝ (Fin r) := fun x => WithLp.toLp 2 (p x)
  let Q : Y → EuclideanSpace ℝ (Fin r) := fun y => WithLp.toLp 2 (q y)
  have hPn : ∀ x, ‖P x‖ ^ 2 = p x ⬝ᵥ p x := fun x => by
    rw [← real_inner_self_eq_norm_sq, ip_toLp]
  have hQn : ∀ y, ‖Q y‖ ^ 2 = q y ⬝ᵥ q y := fun y => by
    rw [← real_inner_self_eq_norm_sq, ip_toLp]
  have hPne : ∀ x, ‖P x‖ ≠ 0 := fun x h => by
    have := hPn x; rw [h] at this; have := hppos x; linarith
  have hQne : ∀ y, ‖Q y‖ ≠ 0 := fun y h => by
    have := hQn y; rw [h] at this; have := hqpos y; linarith
  have hPpos : ∀ x, 0 < ‖P x‖ := fun x => lt_of_le_of_ne (norm_nonneg _) (Ne.symm (hPne x))
  have hQpos : ∀ y, 0 < ‖Q y‖ := fun y => lt_of_le_of_ne (norm_nonneg _) (Ne.symm (hQne y))
  have hinner : ∀ x y, inner ℝ ((‖P x‖⁻¹) • P x) ((‖Q y‖⁻¹) • Q y) =
      (‖P x‖⁻¹ * ‖Q y‖⁻¹) * (w x ⬝ᵥ v y) := by
    intro x y
    rw [real_inner_smul_left, real_inner_smul_right, ← hpq]
    simp only [P, Q, ip_toLp]
    ring
  refine ⟨fun x => (‖P x‖⁻¹) • P x, fun y => (‖Q y‖⁻¹) • Q y, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro x; rw [norm_smul, norm_inv, norm_norm]; exact inv_mul_cancel₀ (hPne x)
  · intro y; rw [norm_smul, norm_inv, norm_norm]; exact inv_mul_cancel₀ (hQne y)
  · intro x y
    beta_reduce
    rw [hinner]
    have hc : 0 < ‖P x‖⁻¹ * ‖Q y‖⁻¹ := by have := hPpos x; have := hQpos y; positivity
    have := hF x y
    split_ifs at this ⊢
    · exact mul_pos hc this
    · exact mul_neg_of_pos_of_neg hc this
  · have hcol : ∀ y, ∑ x, |inner ℝ ((‖P x‖⁻¹) • P x) ((‖Q y‖⁻¹) • Q y)| ^ 2 =
        (Fintype.card X : ℝ) / r := by
      intro y
      have hQy : ‖Q y‖ ^ 2 = ∑ x, a x * (w x ⬝ᵥ v y) ^ 2 := by rw [hQn, hqq]
      have hQy0 : 0 < ‖Q y‖ ^ 2 := by have := hQpos y; positivity
      have hterm : ∀ x, |inner ℝ ((‖P x‖⁻¹) • P x) ((‖Q y‖⁻¹) • Q y)| ^ 2 =
          ((Fintype.card X : ℝ) / r) * (a x * (w x ⬝ᵥ v y) ^ 2) / ‖Q y‖ ^ 2 := by
        intro x
        rw [hinner, sq_abs]
        have hPx : ‖P x‖ ^ 2 = (r : ℝ) / (Fintype.card X * a x) := by rw [hPn, hlev']
        have hax := ha x
        have h1 := hPpos x
        have h2 := hQpos y
        field_simp
        rw [hPx]
        field_simp
      simp_rw [hterm]
      rw [← Finset.sum_div, ← Finset.mul_sum, ← hQy]
      field_simp
      exact div_self (hQpos y).ne'
    unfold uniformAverage
    simp only [hcol]
    rw [Finset.sum_comm]
    simp only [hcol, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hN : (0 : ℝ) < Fintype.card Y := by
      have : 0 < Fintype.card Y := Fintype.card_pos
      positivity
    field_simp

lemma rank_factor {X Y : Type*} [Fintype X] [Fintype Y] (H : Matrix X Y ℝ) (r : ℕ)
    (hr : H.rank = r) :
    ∃ (U : X → Fin r → ℝ) (V : Y → Fin r → ℝ), ∀ x y, H x y = U x ⬝ᵥ V y := by
  classical
  have hfin : Module.finrank ℝ (Submodule.span ℝ (Set.range H.col)) = r := by
    rw [← Matrix.rank_eq_finrank_span_cols]; exact hr
  let b := Module.finBasisOfFinrankEq ℝ (Submodule.span ℝ (Set.range H.col)) hfin
  have hmem : ∀ y, (H.col y) ∈ Submodule.span ℝ (Set.range H.col) :=
    fun y => Submodule.subset_span ⟨y, rfl⟩
  refine ⟨fun x j => ((b j : Submodule.span ℝ (Set.range H.col)) : X → ℝ) x,
    fun y j => b.repr ⟨H.col y, hmem y⟩ j, fun x y => ?_⟩
  have h1 := b.sum_repr ⟨H.col y, hmem y⟩
  have h2 := congrArg (fun z : Submodule.span ℝ (Set.range H.col) => (z : X → ℝ) x) h1
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at h2
  simp only [dotProduct]
  have h3 : H x y = H.col y x := rfl
  rw [h3, ← h2]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

lemma det_ne_zero_dense {X : Type*} [Fintype X] {r : ℕ} (f : Fin r → X)
    (hf : Function.Injective f) :
    Dense {w : X → Fin r → ℝ | (Matrix.of fun i j => w (f i) j).det ≠ 0} := by
  classical
  rw [dense_iff_inter_open]
  intro U hU ⟨w0, hw0⟩
  let e : X → Fin r → ℝ := fun x j => if f j = x then 1 else 0
  let φ : ℝ → (X → Fin r → ℝ) := fun t => w0 + t • e
  have hφ : Continuous φ := continuous_const.add (continuous_id.smul continuous_const)
  have hφ0 : φ 0 = w0 := by simp [φ]
  have hU' : IsOpen (φ ⁻¹' U) := hU.preimage hφ
  have h0 : (0 : ℝ) ∈ φ ⁻¹' U := by simpa [hφ0] using hw0
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU' 0 h0
  set W0 : Matrix (Fin r) (Fin r) ℝ := Matrix.of fun i j => w0 (f i) j with hW0
  have hdet : ∀ t : ℝ, (Matrix.of fun i j => φ t (f i) j).det =
      ((-W0).charpoly).eval t := by
    intro t
    rw [Matrix.eval_charpoly]
    congr 1
    ext i j
    simp [φ, hW0, e, hf.eq_iff, Matrix.sub_apply, Matrix.diagonal_apply, eq_comm, add_comm]
  have hfin : Set.Finite {t : ℝ | ((-W0).charpoly).IsRoot t} :=
    Polynomial.finite_setOfPred_isRoot (Matrix.charpoly_monic _).ne_zero
  have hinf : (Set.Ioo (-ε) ε).Infinite := Set.Ioo_infinite (by linarith)
  obtain ⟨t, ht, htn⟩ := (hinf.sdiff hfin).nonempty
  refine ⟨φ t, hball ?_, ?_⟩
  · rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact ⟨by linarith [ht.1], ht.2⟩
  · show (Matrix.of fun i j => φ t (f i) j).det ≠ 0
    rw [hdet]
    exact htn

lemma exists_genpos {X Y : Type*} [Fintype X] [Fintype Y] {r : ℕ} (F : Matrix X Y Bool)
    (U : X → Fin r → ℝ) (v : Y → Fin r → ℝ) (hU : StrictRealizes F (fun x y => U x ⬝ᵥ v y)) :
    ∃ w : X → Fin r → ℝ, GenPos w ∧ StrictRealizes F (fun x y => w x ⬝ᵥ v y) := by
  classical
  let O : Set (X → Fin r → ℝ) := {w | StrictRealizes F (fun x y => w x ⬝ᵥ v y)}
  have hcont : ∀ x y, Continuous fun w : X → Fin r → ℝ => w x ⬝ᵥ v y := fun x y =>
    continuous_finsetSum _ fun i _ =>
      (((continuous_apply i).comp (continuous_apply x) :
        Continuous fun w : X → Fin r → ℝ => w x i)).mul continuous_const
  have hO : IsOpen O := by
    have : O = ⋂ x, ⋂ y, {w : X → Fin r → ℝ |
        if F x y then 0 < w x ⬝ᵥ v y else w x ⬝ᵥ v y < 0} := by
      ext w; simp [O, StrictRealizes]
    rw [this]
    refine isOpen_iInter_of_finite fun x => isOpen_iInter_of_finite fun y => ?_
    by_cases h : F x y
    · simp only [h, if_true]; exact isOpen_lt continuous_const (hcont x y)
    · simp only [h, if_false]; exact isOpen_lt (hcont x y) continuous_const
  let G : Set (X → Fin r → ℝ) := ⋂ f : {f : Fin r → X // Function.Injective f},
    {w | (Matrix.of fun i j => w (f.1 i) j).det ≠ 0}
  have hGd : Dense G := by
    refine dense_iInter_of_isOpen (fun f => ?_) (fun f => det_ne_zero_dense f.1 f.2)
    have hc : Continuous fun w : X → Fin r → ℝ => (Matrix.of fun i j => w (f.1 i) j).det := by
      refine Continuous.matrix_det ?_
      refine continuous_pi fun i => continuous_pi fun j => ?_
      exact (continuous_apply j).comp (continuous_apply (f.1 i))
    exact isOpen_ne_fun hc continuous_const
  obtain ⟨w, hwO, hwG⟩ := hGd.inter_open_nonempty O hO ⟨U, hU⟩
  refine ⟨w, fun f hf => ?_, hwO⟩
  have := Set.mem_iInter.1 hwG ⟨f, hf⟩
  exact this

theorem main {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (F : Matrix X Y Bool) (r : ℕ) (hr : signRank F = r) :
    ∃ (u : X → EuclideanSpace ℝ (Fin r)) (v : Y → EuclideanSpace ℝ (Fin r)),
      UnitRealization F r u v ∧
      uniformAverage (fun x y => |inner ℝ (u x) (v y)| ^ 2) = 1 / (r : ℝ) := by
  classical
  have hex : ∃ r' : ℕ, ∃ H : Matrix X Y ℝ, StrictRealizes F H ∧ H.rank = r' :=
    ⟨(canonicalRealization F).rank, canonicalRealization F, by
      intro x y
      cases hF : F x y <;> norm_num [canonicalRealization, hF], rfl⟩
  have hsr : signRank F = Nat.find hex := rfl
  obtain ⟨H, hH, hrk⟩ := Nat.find_spec hex
  rw [← hsr, hr] at hrk
  obtain ⟨U, V, hUV⟩ := rank_factor H r hrk
  have hU : StrictRealizes F (fun x y => U x ⬝ᵥ V y) := by
    intro x y
    have := hH x y
    simpa [hUV x y] using this
  have hr1 : 1 ≤ r := by
    by_contra h0
    have : r = 0 := by omega
    subst this
    obtain ⟨x⟩ := ‹Nonempty X›
    obtain ⟨y⟩ := ‹Nonempty Y›
    have := hU x y
    simp [dotProduct] at this
  have hrM : r ≤ Fintype.card X := by
    have h1 := Matrix.rank_le_card_height H
    omega
  obtain ⟨w, hgp, hw⟩ := exists_genpos F U V hU
  exact final_step F w V hgp hr1 hrM hw

end SignRankMargin.OREquality.Dev.L11

namespace SignRankMargin.OREquality

theorem chk_lemma_11 {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (F : Matrix X Y Bool) (r : ℕ) (hr : signRank F = r) :
    ∃ (u : X → EuclideanSpace ℝ (Fin r)) (v : Y → EuclideanSpace ℝ (Fin r)),
      UnitRealization F r u v ∧
      uniformAverage (fun x y => |inner ℝ (u x) (v y)| ^ 2) = 1 / (r : ℝ) :=
  Dev.L11.main F r hr

end SignRankMargin.OREquality
end

theorem solution : type_of% @SignRankMargin.OREquality.chk_lemma_11 := @SignRankMargin.OREquality.chk_lemma_11
