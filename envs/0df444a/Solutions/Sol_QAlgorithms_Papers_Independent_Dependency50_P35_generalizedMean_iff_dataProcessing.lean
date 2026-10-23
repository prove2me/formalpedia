-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P35.generalizedMean_iff_dataProcessing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T12:27:22.634207+00:00
-- url     : https://prove2.me/submissions/82f198e1-142a-43cc-951d-188fef3b3b4a

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P35
open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

namespace X7G

lemma dom_iff {I : Type} [Fintype I] [DecidableEq I] (σ ρ : Mat I) :
    Dominates σ ρ ↔ ∀ v, σ.mulVec v = 0 → ρ.mulVec v = 0 := by
  unfold Dominates
  constructor
  · intro h v hv
    have := h (show v ∈ LinearMap.ker σ.mulVecLin by simpa [LinearMap.mem_ker] using hv)
    simpa [LinearMap.mem_ker] using this
  · intro h v hv
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
    exact h v hv

lemma cpos {r : ℝ} (hr : 0 ≤ r) : (0:ℂ) ≤ (r:ℂ) := Complex.zero_le_real.mpr hr

lemma domain_smul {I : Type} [Fintype I] [DecidableEq I] {ρ σ : Mat I} (h : Domain ρ σ)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    Domain ((r:ℂ) • ρ) ((s:ℂ) • σ) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1.smul (cpos hr.le), h2.smul (cpos hs.le), ?_, ?_⟩
  · exact smul_ne_zero (by exact_mod_cast hr.ne') h3
  · rw [dom_iff] at h4 ⊢
    intro v hv
    rw [Matrix.smul_mulVec] at hv ⊢
    have : σ.mulVec v = 0 := by
      have hs' : (s:ℂ) ≠ 0 := by exact_mod_cast hs.ne'
      exact (smul_eq_zero.mp hv).resolve_left hs'
    rw [h4 v this, smul_zero]

lemma D_self {D : DivergenceFamily} {g : ℝ → ℝ} (hA : SixAxioms D g)
    {I : Type} [Fintype I] [DecidableEq I] (ρ : Mat I) (h : Domain ρ ρ) : D I ρ ρ = 0 := by
  have := (hA.2.2.2.2.2.1 I ρ ρ h)
  have z : (ρ - ρ).PosSemidef := by rw [sub_self]; exact Matrix.PosSemidef.zero
  exact le_antisymm (this.2 z) (this.1 z)

lemma domain_scalar {c : ℝ} (hc : 0 < c) : Domain ((c:ℂ) • (1 : Mat (Fin 1))) ((c:ℂ) • (1 : Mat (Fin 1))) := by
  refine ⟨Matrix.PosSemidef.one.smul (cpos hc.le), Matrix.PosSemidef.one.smul (cpos hc.le), ?_, le_rfl⟩
  exact smul_ne_zero (by exact_mod_cast hc.ne') one_ne_zero

lemma D_smul {D : DivergenceFamily} {g : ℝ → ℝ} (hA : SixAxioms D g)
    {I : Type} [Fintype I] [DecidableEq I] (ρ σ : Mat I) (h : Domain ρ σ) (c : ℝ) (hc : 0 < c) :
    D I ((c:ℂ) • ρ) ((c:ℂ) • σ) = D I ρ σ := by
  have hτ := domain_scalar hc
  have e1 := hA.2.2.2.2.2.2.1 I (Fin 1) ρ σ _ _ h hτ
  rw [D_self hA _ hτ, add_zero] at e1
  let U : Matrix (I × Fin 1) I ℂ := Matrix.of fun p i => if p.1 = i then 1 else 0
  have hU1 : Uᴴ * U = 1 := by
    ext i j
    simp [U, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, Fintype.sum_prod_type]
    by_cases hij : j = i
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  have hU2 : U * Uᴴ = 1 := by
    ext ⟨i, a⟩ ⟨j, b⟩
    have hab : a = b := Subsingleton.elim _ _
    subst hab
    simp [U, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
  have e2 := hA.2.2.2.1 I (I × Fin 1) _ _ U (domain_smul h hc hc) hU1 hU2
  have k1 : U * ((c:ℂ) • ρ) * Uᴴ = Matrix.kronecker ρ ((c:ℂ) • (1 : Mat (Fin 1))) := by
    ext ⟨i, a⟩ ⟨j, b⟩
    have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    subst ha hb
    simp [U, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kronecker, Matrix.kroneckerMap_apply]
    ring
  have k2 : U * ((c:ℂ) • σ) * Uᴴ = Matrix.kronecker σ ((c:ℂ) • (1 : Mat (Fin 1))) := by
    ext ⟨i, a⟩ ⟨j, b⟩
    have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    subst ha hb
    simp [U, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kronecker, Matrix.kroneckerMap_apply]
    ring
  rw [k1, k2] at e2
  rw [e2]
  convert e1 using 2


def krSel {I : Type} [DecidableEq I] : Fin 2 → Matrix I (I ⊕ I) ℂ := fun b => Matrix.of fun i k =>
  if b = 0 then (if k = Sum.inl i then 1 else 0) else (if k = Sum.inr i then 1 else 0)

lemma krSel_kraus {I : Type} [Fintype I] [DecidableEq I] :
    QAlgorithms.IsKrausFamily (krSel (I := I)) := by
  unfold QAlgorithms.IsKrausFamily
  ext k k'
  rcases k with i | i <;> rcases k' with j | j <;>
    simp [krSel, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Matrix.sum_apply,
      Matrix.conjTranspose_apply]

lemma krSel_apply {I : Type} [Fintype I] [DecidableEq I] (X : Mat (I ⊕ I)) :
    QAlgorithms.krausApply krSel X = Matrix.of fun i j => X (.inl i) (.inl j) + X (.inr i) (.inr j) := by
  ext i j
  simp [QAlgorithms.krausApply, krSel, Matrix.mul_apply, Fin.sum_univ_two, Matrix.sum_apply,
    Matrix.conjTranspose_apply, Fintype.sum_sum_type]

lemma directSum_eq {I : Type} [Fintype I] [DecidableEq I] (X Y : Mat I) :
    directSum X Y = (krSel (I := I) 0)ᴴ * X * krSel (I := I) 0 + (krSel (I := I) 1)ᴴ * Y * krSel (I := I) 1 := by
  ext k k'
  rcases k with i | i <;> rcases k' with j | j <;>
    simp [directSum, krSel, Matrix.mul_apply, Matrix.conjTranspose_apply]

lemma directSum_psd {I : Type} [Fintype I] [DecidableEq I] {X Y : Mat I}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) : (directSum X Y).PosSemidef := by
  rw [directSum_eq]
  exact (hX.conjTranspose_mul_mul_same _).add (hY.conjTranspose_mul_mul_same _)

lemma directSum_mulVec_inl {I : Type} [Fintype I] (X Y : Mat I) (v : I ⊕ I → ℂ) (i : I) :
    (directSum X Y).mulVec v (.inl i) = X.mulVec (v ∘ Sum.inl) i := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, directSum]

lemma directSum_mulVec_inr {I : Type} [Fintype I] (X Y : Mat I) (v : I ⊕ I → ℂ) (i : I) :
    (directSum X Y).mulVec v (.inr i) = Y.mulVec (v ∘ Sum.inr) i := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, directSum]

lemma domain_directSum {I : Type} [Fintype I] [DecidableEq I] {ρ σ τ ω : Mat I}
    (h1 : Domain ρ σ) (h2 : Domain τ ω) : Domain (directSum ρ τ) (directSum σ ω) := by
  refine ⟨directSum_psd h1.1 h2.1, directSum_psd h1.2.1 h2.2.1, ?_, ?_⟩
  · intro h0
    apply h1.2.2.1
    ext i j
    have := congrFun (congrFun h0 (.inl i)) (.inl j)
    simpa [directSum] using this
  · rw [dom_iff]
    intro v hv
    have a1 : σ.mulVec (v ∘ Sum.inl) = 0 := by
      funext i; have := congrFun hv (.inl i); rwa [directSum_mulVec_inl] at this
    have a2 : ω.mulVec (v ∘ Sum.inr) = 0 := by
      funext i; have := congrFun hv (.inr i); rwa [directSum_mulVec_inr] at this
    have b1 := (dom_iff _ _).1 h1.2.2.2 _ a1
    have b2 := (dom_iff _ _).1 h2.2.2.2 _ a2
    funext k
    rcases k with i | i
    · rw [directSum_mulVec_inl, b1]; rfl
    · rw [directSum_mulVec_inr, b2]; rfl

lemma tr_smul {I : Type} [Fintype I] (c : ℝ) (X : Mat I) : tr ((c:ℂ) • X) = c * tr X := by
  simp [tr, Matrix.trace_smul]

theorem dpi_to_conv {D : DivergenceFamily} {g : ℝ → ℝ} (hA : SixAxioms D g)
    (hDPI : FamilyDPI D) : GeneralMeanConvexity D g := by
  intro I _ _ ρ σ τ ω h1 h2 d1 d2 d3 d4 l hl0 hl1
  simp only
  rcases eq_or_lt_of_le hl0 with hl | hl
  · subst hl
    have e1 : ((0:ℝ):ℂ) • ρ + ((1-0:ℝ):ℂ) • τ = τ := by simp
    have e2 : ((0:ℝ):ℂ) • σ + ((1-0:ℝ):ℂ) • ω = ω := by simp
    rw [e1, e2]; constructor <;> intro _ <;> simp
  rcases eq_or_lt_of_le hl1 with hl' | hl'
  · subst hl'
    have e1 : ((1:ℝ):ℂ) • ρ + ((1-1:ℝ):ℂ) • τ = ρ := by simp
    have e2 : ((1:ℝ):ℂ) • σ + ((1-1:ℝ):ℂ) • ω = σ := by simp
    rw [e1, e2]; constructor <;> intro _ <;> simp
  have hl2 : 0 < 1 - l := by linarith
  have dA := domain_smul h1 hl hl
  have dB := domain_smul h2 hl2 hl2
  have hE : QAlgorithms.IsChannel (QAlgorithms.krausApply (krSel (I := I))) :=
    ⟨2, krSel, krSel_kraus, fun _ => rfl⟩
  have hd := hDPI (I ⊕ I) I _ hE _ _ (domain_directSum dA dB)
  rw [krSel_apply, krSel_apply] at hd
  have em1 : (Matrix.of fun i j => directSum ((l:ℂ) • ρ) (((1-l:ℝ):ℂ) • τ) (.inl i) (.inl j) +
      directSum ((l:ℂ) • ρ) (((1-l:ℝ):ℂ) • τ) (.inr i) (.inr j)) = (l:ℂ) • ρ + ((1-l:ℝ):ℂ) • τ := by
    ext i j; simp [directSum]
  have em2 : (Matrix.of fun i j => directSum ((l:ℂ) • σ) (((1-l:ℝ):ℂ) • ω) (.inl i) (.inl j) +
      directSum ((l:ℂ) • σ) (((1-l:ℝ):ℂ) • ω) (.inr i) (.inr j)) = (l:ℂ) • σ + ((1-l:ℝ):ℂ) • ω := by
    ext i j; simp [directSum]
  rw [em1, em2] at hd
  have t1 : tr ((l:ℂ) • ρ) = l := by rw [tr_smul, d1.2, mul_one]
  have t2 : tr (((1-l:ℝ):ℂ) • τ) = 1 - l := by rw [tr_smul, d3.2, mul_one]
  have t3 : tr ((l:ℂ) • σ) = l := by rw [tr_smul, d2.2, mul_one]
  have t4 : tr (((1-l:ℝ):ℂ) • ω) = 1 - l := by rw [tr_smul, d4.2, mul_one]
  have hm := hA.2.2.2.2.2.2.2 I I _ _ _ _ dA dB (by rw [t1, t2]; linarith) (by rw [t3, t4]; linarith)
  rw [t1, t2, D_smul hA _ _ h1 l hl, D_smul hA _ _ h2 (1-l) hl2] at hm
  have hm' : g (D (I ⊕ I) (directSum ((l:ℂ) • ρ) (((1-l:ℝ):ℂ) • τ))
      (directSum ((l:ℂ) • σ) (((1-l:ℝ):ℂ) • ω))) = l * g (D I ρ σ) + (1 - l) * g (D I τ ω) := by
    rw [hm]; field_simp; ring_nf
  constructor
  · intro hg
    rw [← hm']
    exact hg.monotone hd
  · intro hg
    rw [← hm']
    exact hg.antitone hd


lemma psd_sum_ker {ι L : Type} [Fintype L] (s : Finset ι) (A : ι → Mat L)
    (hA : ∀ k, (A k).PosSemidef) (v : L → ℂ)
    (h : (∑ k ∈ s, A k).mulVec v = 0) : ∀ k ∈ s, (A k).mulVec v = 0 := by
  have h1 : star v ⬝ᵥ (∑ k ∈ s, A k).mulVec v = 0 := by rw [h, dotProduct_zero]
  rw [Matrix.sum_mulVec, dotProduct_sum] at h1
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => (hA k).dotProduct_mulVec_nonneg v)).1 h1
  intro k hk
  exact ((hA k).dotProduct_mulVec_zero_iff v).1 (h2 k hk)

lemma conj_ker {I J : Type} [Fintype I] [Fintype J] {A : Mat I} (hA : A.PosSemidef)
    (F : Matrix J I ℂ) (v : J → ℂ) (h : (F * A * Fᴴ).mulVec v = 0) :
    A.mulVec (Fᴴ.mulVec v) = 0 := by
  rw [← hA.dotProduct_mulVec_zero_iff]
  have h1 : star v ⬝ᵥ (F * A * Fᴴ).mulVec v = 0 := by rw [h, dotProduct_zero]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec] at h1
  rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
  exact h1

lemma domain_kraus {ι I J : Type} [Fintype ι] [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] (F : ι → Matrix J I ℂ) (hF : ∑ k, (F k)ᴴ * F k = 1) {ρ σ : Mat I}
    (h : Domain ρ σ) : Domain (∑ k, F k * ρ * (F k)ᴴ) (∑ k, F k * σ * (F k)ᴴ) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨Matrix.posSemidef_sum _ (fun k _ => h1.mul_mul_conjTranspose_same _),
    Matrix.posSemidef_sum _ (fun k _ => h2.mul_mul_conjTranspose_same _), ?_, ?_⟩
  · intro h0
    apply h3
    rw [← h1.trace_eq_zero_iff]
    have : (∑ k, F k * ρ * (F k)ᴴ).trace = ρ.trace := by
      rw [Matrix.trace_sum]
      simp_rw [Matrix.trace_mul_comm _ (F _)ᴴ, ← Matrix.mul_assoc, ← Matrix.trace_sum,
        ← Finset.sum_mul, hF, Matrix.one_mul]
    rw [← this, h0, Matrix.trace_zero]
  · rw [dom_iff] at h4 ⊢
    intro v hv
    have := psd_sum_ker _ _ (fun k => h2.mul_mul_conjTranspose_same (F k)) v hv
    rw [Matrix.sum_mulVec]
    apply Finset.sum_eq_zero
    intro k hk
    have a := h4 _ (conj_ker h2 (F k) v (this k hk))
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, a, Matrix.mulVec_zero]

lemma domain_isom {I L : Type} [Fintype I] [Fintype L] [DecidableEq I] [DecidableEq L]
    (V : Matrix L I ℂ) (hV : Vᴴ * V = 1) {ρ σ : Mat I} (h : Domain ρ σ) :
    Domain (V * ρ * Vᴴ) (V * σ * Vᴴ) := by
  have := domain_kraus (ι := Unit) (fun _ => V) (by simpa using hV) h
  simpa using this

lemma trace_isom {I L : Type} [Fintype I] [Fintype L] [DecidableEq I]
    (V : Matrix L I ℂ) (hV : Vᴴ * V = 1) (ρ : Mat I) : (V * ρ * Vᴴ).trace = ρ.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul]

/-- equivalence S × Bool ≃ S ⊕ S -/
def bs (S : Type) : S × Bool ≃ S ⊕ S where
  toFun q := if q.2 then .inl q.1 else .inr q.1
  invFun p := Sum.elim (fun s => (s, true)) (fun s => (s, false)) p
  left_inv q := by rcases q with ⟨s, _ | _⟩ <;> rfl
  right_inv p := by rcases p with s | s <;> rfl

lemma ds_fromBlocks {S : Type} (X Y : Mat S) : directSum X Y = Matrix.fromBlocks X 0 0 Y := by
  ext p q; rcases p with i | i <;> rcases q with j | j <;> rfl

lemma D_directSum_zero {D : DivergenceFamily} {g : ℝ → ℝ} (hA : SixAxioms D g)
    {S : Type} [Fintype S] [DecidableEq S] (X X' : Mat S) (h : Domain X X') :
    D (S ⊕ S) (directSum X 0) (directSum X' 0) = D S X X' := by
  -- rank-one projector on Bool
  let a : Matrix Bool Unit ℂ := Matrix.of fun b _ => if b = true then 1 else 0
  have ha : aᴴ * a = 1 := by ext u v; simp [a, Matrix.mul_apply, Fintype.sum_bool]
  have hU1 : Domain (1 : Mat Unit) 1 := ⟨Matrix.PosSemidef.one, Matrix.PosSemidef.one, one_ne_zero, le_rfl⟩
  have hQ := domain_isom a ha hU1
  have e1 := hA.2.2.2.2.2.2.1 S Bool X X' _ _ h hQ
  rw [D_self hA _ hQ, add_zero] at e1
  -- isometry S → S × Bool
  let b : Matrix (S × Bool) S ℂ := Matrix.of fun q s => if q.1 = s ∧ q.2 = true then 1 else 0
  have hb : bᴴ * b = 1 := by
    ext s t
    simp [b, Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_bool, Matrix.one_apply]
    by_cases hst : s = t
    · subst hst; simp
    · simp [hst, Ne.symm hst]
  have kX : ∀ Y : Mat S, Matrix.kronecker Y (a * (1 : Mat Unit) * aᴴ) = b * Y * bᴴ := by
    intro Y
    ext ⟨s, x⟩ ⟨t, y⟩
    cases x <;> cases y <;> simp [a, b, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Fintype.sum_prod_type, Fintype.sum_bool]
  rw [kX, kX] at e1
  let R : Matrix (S ⊕ S) (S × Bool) ℂ := Matrix.of fun p q => if q = (bs S).symm p then 1 else 0
  have hRM : ∀ M : Mat (S × Bool), R * M * Rᴴ = Matrix.of fun p p' => M ((bs S).symm p) ((bs S).symm p') := by
    intro M; ext p p'
    simp [R, Matrix.mul_apply]
  have hR1 : Rᴴ * R = 1 := by
    ext q q'
    simp only [R, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
    rw [← (bs S).sum_comp]
    simp
  have hR2 : R * Rᴴ = 1 := by
    ext p p'
    simp [R, Matrix.mul_apply, Matrix.one_apply]
    by_cases hpp : p = p'
    · subst hpp; simp
    · simp [hpp, Ne.symm hpp]
  have e2 := hA.2.2.2.1 (S × Bool) (S ⊕ S) _ _ R (domain_isom b hb h) hR1 hR2
  have k3 : ∀ Y : Mat S, R * (b * Y * bᴴ) * Rᴴ = directSum Y 0 := by
    intro Y
    rw [hRM]
    ext p p'
    rcases p with i | i <;> rcases p' with j | j <;>
      simp [bs, b, directSum, Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_bool]
  rw [k3, k3] at e2
  rw [← e2]
  convert e1 using 2

lemma halmos_unitary {S : Type} [Fintype S] [DecidableEq S] (T : Mat S) (h : T * Tᴴ * T = T) :
    (Matrix.fromBlocks T (1 - T * Tᴴ) (1 - Tᴴ * T) (-Tᴴ))ᴴ *
        Matrix.fromBlocks T (1 - T * Tᴴ) (1 - Tᴴ * T) (-Tᴴ) = 1 ∧
    Matrix.fromBlocks T (1 - T * Tᴴ) (1 - Tᴴ * T) (-Tᴴ) *
        (Matrix.fromBlocks T (1 - T * Tᴴ) (1 - Tᴴ * T) (-Tᴴ))ᴴ = 1 := by
  have h' : Tᴴ * T * Tᴴ = Tᴴ := by
    have := congrArg Matrix.conjTranspose h
    simpa [Matrix.conjTranspose_mul, Matrix.mul_assoc] using this
  have hc1 : (1 - T * Tᴴ)ᴴ = 1 - T * Tᴴ := by simp [Matrix.conjTranspose_sub]
  have hc2 : (1 - Tᴴ * T)ᴴ = 1 - Tᴴ * T := by simp [Matrix.conjTranspose_sub]
  rw [Matrix.fromBlocks_conjTranspose, hc1, hc2, Matrix.conjTranspose_neg,
    Matrix.conjTranspose_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
    ← Matrix.fromBlocks_one]
  constructor
  · rw [Matrix.fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩
    · calc Tᴴ * T + (1 - Tᴴ * T) * (1 - Tᴴ * T) = 1 - Tᴴ * T + Tᴴ * (T * Tᴴ * T) := by noncomm_ring
        _ = 1 := by rw [h]; abel
    · noncomm_ring
    · noncomm_ring
    · calc (1 - T * Tᴴ) * (1 - T * Tᴴ) + -T * -Tᴴ = 1 - T * Tᴴ + (T * Tᴴ * T) * Tᴴ := by noncomm_ring
        _ = 1 := by rw [h]; abel
  · rw [Matrix.fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩
    · calc T * Tᴴ + (1 - T * Tᴴ) * (1 - T * Tᴴ) = 1 - T * Tᴴ + (T * Tᴴ * T) * Tᴴ := by noncomm_ring
        _ = 1 := by rw [h]; abel
    · noncomm_ring
    · noncomm_ring
    · calc (1 - Tᴴ * T) * (1 - Tᴴ * T) + -Tᴴ * -T = 1 - Tᴴ * T + Tᴴ * (T * Tᴴ * T) := by noncomm_ring
        _ = 1 := by rw [h]; abel

lemma halmos_action {S : Type} [Fintype S] [DecidableEq S] (T X : Mat S)
    (h1 : (1 - Tᴴ * T) * X = 0) (h2 : X * (1 - Tᴴ * T) = 0) :
    Matrix.fromBlocks T (1 - T * Tᴴ) (1 - Tᴴ * T) (-Tᴴ) * directSum X 0 *
        (Matrix.fromBlocks T (1 - T * Tᴴ) (1 - Tᴴ * T) (-Tᴴ))ᴴ = directSum (T * X * Tᴴ) 0 := by
  rw [ds_fromBlocks, ds_fromBlocks, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, add_zero, h1, Matrix.fromBlocks_multiply, Matrix.zero_mul, zero_add]
  have : T * X * (1 - Tᴴ * T)ᴴ = 0 := by
    rw [show (1 - Tᴴ * T)ᴴ = 1 - Tᴴ * T by simp [Matrix.conjTranspose_sub], Matrix.mul_assoc, h2,
      Matrix.mul_zero]
  rw [this]

lemma D_isom {D : DivergenceFamily} {g : ℝ → ℝ} (hA : SixAxioms D g)
    {I L : Type} [Fintype I] [Fintype L] [DecidableEq I] [DecidableEq L]
    (V : Matrix L I ℂ) (hV : Vᴴ * V = 1) {ρ σ : Mat I} (h : Domain ρ σ) :
    D L (V * ρ * Vᴴ) (V * σ * Vᴴ) = D I ρ σ := by
  have hI : Nonempty I := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    exact h.2.2.1 (Matrix.ext fun i => isEmptyElim i)
  obtain ⟨i0⟩ := hI
  have hL : Nonempty L := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have := congrFun (congrFun hV i0) i0
    simp [Matrix.mul_apply] at this
  obtain ⟨l0⟩ := hL
  let A : Matrix (L × I) I ℂ := Matrix.of fun q i => if q.1 = l0 ∧ q.2 = i then 1 else 0
  let B : Matrix (L × I) I ℂ := Matrix.of fun q i => if q.2 = i0 then V q.1 i else 0
  have hA1 : Aᴴ * A = 1 := by
    ext i j
    simp [A, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, ite_and]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  have hB1 : Bᴴ * B = 1 := by
    rw [← hV]
    ext i j
    simp [B, Matrix.mul_apply, Fintype.sum_prod_type]
  have hA' : ∀ {n : Type} (M : Matrix I n ℂ), Aᴴ * (A * M) = M := by
    intro n M; rw [← Matrix.mul_assoc, hA1, Matrix.one_mul]
  have hB' : ∀ {n : Type} (M : Matrix I n ℂ), Bᴴ * (B * M) = M := by
    intro n M; rw [← Matrix.mul_assoc, hB1, Matrix.one_mul]
  set T : Mat (L × I) := B * Aᴴ with hT
  have hTT : Tᴴ * T = A * Aᴴ := by
    rw [hT, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc, hB']
  have hTTT : T * Tᴴ * T = T := by
    rw [Matrix.mul_assoc, hTT, hT]
    simp only [Matrix.mul_assoc, hA']
  have act : ∀ Y : Mat I, Matrix.fromBlocks T (1 - T * Tᴴ) (1 - Tᴴ * T) (-Tᴴ) *
      directSum (A * Y * Aᴴ) 0 * (Matrix.fromBlocks T (1 - T * Tᴴ) (1 - Tᴴ * T) (-Tᴴ))ᴴ =
      directSum (B * Y * Bᴴ) 0 := by
    intro Y
    rw [halmos_action]
    · congr 1
      rw [hT, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      simp only [Matrix.mul_assoc, hA']
    · rw [hTT, Matrix.sub_mul, Matrix.one_mul]
      simp only [Matrix.mul_assoc, hA']
      simp
    · rw [hTT, Matrix.mul_sub, Matrix.mul_one]
      simp only [Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hA']
      simp
  obtain ⟨hW1, hW2⟩ := halmos_unitary T hTTT
  -- embed to directSum
  let E : Matrix ((L × I) ⊕ (L × I)) (L × I) ℂ := Matrix.of fun p s => if p = .inl s then 1 else 0
  have hE : Eᴴ * E = 1 := by
    ext s t; simp [E, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
    by_cases hst : s = t
    · subst hst; simp
    · simp [hst, Ne.symm hst]
  have hEds : ∀ Y : Mat (L × I), E * Y * Eᴴ = directSum Y 0 := by
    intro Y; ext p q
    rcases p with i | i <;> rcases q with j | j <;> simp [E, directSum, Matrix.mul_apply]
  have dA := domain_isom A hA1 h
  have dB := domain_isom B hB1 h
  have dEA := domain_isom E hE dA
  rw [hEds, hEds] at dEA
  have s1 := D_directSum_zero hA _ _ dA
  have s2 := D_directSum_zero hA _ _ dB
  have s3 := hA.2.2.2.1 _ _ _ _ _ dEA hW1 hW2
  rw [act, act] at s3
  -- A-side: kron P ρ
  let p : Matrix L Unit ℂ := Matrix.of fun l _ => if l = l0 then 1 else 0
  have hp : pᴴ * p = 1 := by ext u v; simp [p, Matrix.mul_apply]
  let q : Matrix I Unit ℂ := Matrix.of fun i _ => if i = i0 then 1 else 0
  have hq : qᴴ * q = 1 := by ext u v; simp [q, Matrix.mul_apply]
  have hU1 : Domain (1 : Mat Unit) 1 := ⟨Matrix.PosSemidef.one, Matrix.PosSemidef.one, one_ne_zero, le_rfl⟩
  have dp := domain_isom p hp hU1
  have dq := domain_isom q hq hU1
  have kA : ∀ Y : Mat I, A * Y * Aᴴ = Matrix.kronecker (p * (1 : Mat Unit) * pᴴ) Y := by
    intro Y; ext ⟨l, i⟩ ⟨l', i'⟩
    simp [A, p, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, Fintype.sum_prod_type]
    by_cases h1 : l = l0 <;> by_cases h2 : l' = l0 <;> simp [h1, h2]
  have kB : ∀ Y : Mat I, B * Y * Bᴴ = Matrix.kronecker (V * Y * Vᴴ) (q * (1 : Mat Unit) * qᴴ) := by
    intro Y; ext ⟨l, i⟩ ⟨l', i'⟩
    simp [B, q, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, Fintype.sum_prod_type]
    by_cases h1 : i = i0 <;> by_cases h2 : i' = i0 <;> simp [h1, h2]
  have a1 := hA.2.2.2.2.2.2.1 L I _ _ ρ σ dp h
  rw [D_self hA _ dp, zero_add] at a1
  have a2 := hA.2.2.2.2.2.2.1 L I _ _ _ _ (domain_isom V hV h) dq
  rw [D_self hA _ dq, add_zero] at a2
  rw [kA, kA] at s1
  rw [kB, kB] at s2
  rw [kA, kA] at s3
  rw [kB, kB] at s3
  calc D L (V * ρ * Vᴴ) (V * σ * Vᴴ) = _ := a2.symm
    _ = _ := by convert s2.symm using 2
    _ = _ := s3.symm
    _ = _ := by convert s1 using 2
    _ = D I ρ σ := a1


lemma add_ker {L : Type} [Fintype L] {A B : Mat L} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (v : L → ℂ) (h : (A + B).mulVec v = 0) : A.mulVec v = 0 ∧ B.mulVec v = 0 := by
  have h1 : star v ⬝ᵥ (A + B).mulVec v = 0 := by rw [h, dotProduct_zero]
  rw [Matrix.add_mulVec, dotProduct_add] at h1
  have := (add_eq_zero_iff_of_nonneg (hA.dotProduct_mulVec_nonneg v)
    (hB.dotProduct_mulVec_nonneg v)).1 h1
  exact ⟨(hA.dotProduct_mulVec_zero_iff v).1 this.1, (hB.dotProduct_mulVec_zero_iff v).1 this.2⟩

lemma smul_dom {L : Type} [Fintype L] [DecidableEq L] {ρ σ : Mat L} (h : Dominates σ ρ) (c : ℂ)
    (v : L → ℂ) (hv : (c • σ).mulVec v = 0) : (c • ρ).mulVec v = 0 := by
  rw [Matrix.smul_mulVec] at hv ⊢
  rcases smul_eq_zero.mp hv with h0 | h0
  · rw [h0, zero_smul]
  · rw [(dom_iff _ _).1 h v h0, smul_zero]

lemma tr_add {L : Type} [Fintype L] (A B : Mat L) : tr (A + B) = tr A + tr B := by
  simp [tr, Matrix.trace_add]

lemma mix_domain {L : Type} [Fintype L] [DecidableEq L] {ρ σ τ ω : Mat L}
    (h1 : Domain ρ σ) (h2 : Domain τ ω) (d1 : Density ρ) (d2 : Density σ) (d3 : Density τ)
    (d4 : Density ω) (l : ℝ) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    Domain ((l : ℂ) • ρ + ((1-l : ℝ) : ℂ) • τ) ((l : ℂ) • σ + ((1-l : ℝ) : ℂ) • ω) ∧
    Density ((l : ℂ) • ρ + ((1-l : ℝ) : ℂ) • τ) ∧
    Density ((l : ℂ) • σ + ((1-l : ℝ) : ℂ) • ω) := by
  have hl2 : 0 ≤ 1 - l := by linarith
  have p1 := (h1.1.smul (cpos hl0)).add (h2.1.smul (cpos hl2))
  have p2 := (h1.2.1.smul (cpos hl0)).add (h2.2.1.smul (cpos hl2))
  have t1 : tr ((l : ℂ) • ρ + ((1-l : ℝ) : ℂ) • τ) = 1 := by
    rw [tr_add, tr_smul, tr_smul, d1.2, d3.2]; ring
  have t2 : tr ((l : ℂ) • σ + ((1-l : ℝ) : ℂ) • ω) = 1 := by
    rw [tr_add, tr_smul, tr_smul, d2.2, d4.2]; ring
  refine ⟨⟨p1, p2, ?_, ?_⟩, ⟨p1, t1⟩, ⟨p2, t2⟩⟩
  · intro h0; rw [h0] at t1; simp [tr] at t1
  · rw [dom_iff]
    intro v hv
    obtain ⟨a1, a2⟩ := add_ker (h1.2.1.smul (cpos hl0)) (h2.2.1.smul (cpos hl2)) v hv
    rw [Matrix.add_mulVec, smul_dom h1.2.2.2 _ v a1, smul_dom h2.2.2.2 _ v a2, add_zero]

lemma conv_phi {D : DivergenceFamily} {g : ℝ → ℝ} (hA : SixAxioms D g)
    (hC : GeneralMeanConvexity D g) :
    ∃ φ : ℝ → ℝ, StrictMono φ ∧ ∀ (I : Type) [Fintype I] [DecidableEq I] (ρ σ τ ω : Mat I),
      Domain ρ σ → Domain τ ω → Density ρ → Density σ → Density τ → Density ω →
      ∀ l : ℝ, 0 ≤ l → l ≤ 1 →
      φ (D I ((l : ℂ) • ρ + ((1-l : ℝ) : ℂ) • τ) ((l : ℂ) • σ + ((1-l : ℝ) : ℂ) • ω)) ≤
        l * φ (D I ρ σ) + (1-l) * φ (D I τ ω) := by
  rcases hA.2.1 with hm | ha
  · refine ⟨g, hm, ?_⟩
    intro I _ _ ρ σ τ ω h1 h2 d1 d2 d3 d4 l hl0 hl1
    have := hC I ρ σ τ ω h1 h2 d1 d2 d3 d4 l hl0 hl1
    exact this.1 hm
  · refine ⟨fun x => -g x, fun a b hab => neg_lt_neg (ha hab), ?_⟩
    intro I _ _ ρ σ τ ω h1 h2 d1 d2 d3 d4 l hl0 hl1
    have := (hC I ρ σ τ ω h1 h2 d1 d2 d3 d4 l hl0 hl1).2 ha
    simp only at this ⊢
    linarith

def avgM {L G : Type} [Fintype L] (U : G → Mat L) (s : Finset G) (M : Mat L) : Mat L :=
  (((s.card : ℝ)⁻¹ : ℝ) : ℂ) • ∑ x ∈ s, U x * M * (U x)ᴴ

lemma avg_le {D : DivergenceFamily} {g : ℝ → ℝ} (hA : SixAxioms D g) (φ : ℝ → ℝ)
    (hconv : ∀ (I : Type) [Fintype I] [DecidableEq I] (ρ σ τ ω : Mat I),
      Domain ρ σ → Domain τ ω → Density ρ → Density σ → Density τ → Density ω →
      ∀ l : ℝ, 0 ≤ l → l ≤ 1 →
      φ (D I ((l : ℂ) • ρ + ((1-l : ℝ) : ℂ) • τ) ((l : ℂ) • σ + ((1-l : ℝ) : ℂ) • ω)) ≤
        l * φ (D I ρ σ) + (1-l) * φ (D I τ ω))
    {L G : Type} [Fintype L] [DecidableEq L] (U : G → Mat L) (hU1 : ∀ x, (U x)ᴴ * U x = 1)
    (hU2 : ∀ x, U x * (U x)ᴴ = 1) {Y Z : Mat L} (h : Domain Y Z) (dY : Density Y)
    (dZ : Density Z) (s : Finset G) (hs : s.Nonempty) :
    Domain (avgM U s Y) (avgM U s Z) ∧ Density (avgM U s Y) ∧ Density (avgM U s Z) ∧
      φ (D L (avgM U s Y) (avgM U s Z)) ≤ φ (D L Y Z) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
    have e : ∀ M : Mat L, avgM U {a} M = U a * M * (U a)ᴴ := by
      intro M; simp [avgM]
    rw [e, e]
    have hd := domain_isom (U a) (hU1 a) h
    refine ⟨hd, ⟨hd.1, ?_⟩, ⟨hd.2.1, ?_⟩, ?_⟩
    · rw [← dY.2]; simp only [tr]; rw [trace_isom _ (hU1 a)]
    · rw [← dZ.2]; simp only [tr]; rw [trace_isom _ (hU1 a)]
    · rw [← hA.2.2.2.1 L L Y Z (U a) h (hU1 a) (hU2 a)]
  | cons a s ha hs ih =>
    obtain ⟨i1, i2, i3, i4⟩ := ih
    have hnpos : (0:ℝ) < (s.card : ℝ) := by exact_mod_cast hs.card_pos
    have hd := domain_isom (U a) (hU1 a) h
    have dUY : Density (U a * Y * (U a)ᴴ) := ⟨hd.1, by rw [← dY.2]; simp only [tr]; rw [trace_isom _ (hU1 a)]⟩
    have dUZ : Density (U a * Z * (U a)ᴴ) := ⟨hd.2.1, by rw [← dZ.2]; simp only [tr]; rw [trace_isom _ (hU1 a)]⟩
    set l : ℝ := (s.card : ℝ) / ((s.card : ℝ) + 1) with hl
    have hl0 : 0 ≤ l := by positivity
    have hl1 : l ≤ 1 := by rw [hl, div_le_one (by linarith)]; linarith
    have c1 : ((((s.card + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) = (l : ℂ) * ((((s.card : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul]; congr 1; rw [hl]; push_cast; field_simp
    have c2 : ((((s.card + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) = ((1 - l : ℝ) : ℂ) := by
      congr 1; rw [hl]; push_cast; field_simp; ring
    have e : ∀ M : Mat L, avgM U (Finset.cons a s ha) M =
        (l : ℂ) • avgM U s M + ((1 - l : ℝ) : ℂ) • (U a * M * (U a)ᴴ) := by
      intro M
      simp only [avgM, Finset.sum_cons, Finset.card_cons]
      rw [smul_add, smul_smul, ← c1, ← c2, add_comm]
    rw [e, e]
    obtain ⟨m1, m2, m3⟩ := mix_domain i1 hd i2 i3 dUY dUZ l hl0 hl1
    refine ⟨m1, m2, m3, ?_⟩
    have hc := hconv L _ _ _ _ i1 hd i2 i3 dUY dUZ l hl0 hl1
    rw [← hA.2.2.2.1 L L Y Z (U a) h (hU1 a) (hU2 a)] at hc
    have : l * φ (D L (avgM U s Y) (avgM U s Z)) ≤ l * φ (D L Y Z) :=
      mul_le_mul_of_nonneg_left i4 hl0
    linarith


def eps (b : Bool) : ℂ := if b then 1 else -1

lemma eps_mul_self (b : Bool) : eps b * eps b = 1 := by cases b <;> simp [eps]

lemma star_eps (b : Bool) : star (eps b) = eps b := by cases b <;> simp [eps]

@[simp] lemma conj_eps (b : Bool) : (starRingEnd ℂ) (eps b) = eps b := by cases b <;> simp [eps]

lemma eps_not (b : Bool) : eps (!b) = - eps b := by cases b <;> simp [eps]

lemma sign_sum {K : Type} [Fintype K] [DecidableEq K] (x y : K) :
    ∑ s : K → Bool, eps (s x) * eps (s y) = if x = y then (Fintype.card (K → Bool) : ℂ) else 0 := by
  by_cases hxy : x = y
  · subst hxy; simp [eps_mul_self]
  · rw [if_neg hxy]
    let f : (K → Bool) → (K → Bool) := fun s => Function.update s x (!s x)
    have hf : Function.Involutive f := by
      intro s; funext z
      by_cases hz : z = x
      · subst hz; simp [f]
      · simp [f, hz]
    have key : ∑ s : K → Bool, eps (s x) * eps (s y) = - ∑ s : K → Bool, eps (s x) * eps (s y) := by
      conv_lhs => rw [← Equiv.sum_comp (hf.toPerm f)]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro s _
      simp only [Function.Involutive.coe_toPerm, f, Function.update_self,
        Function.update_of_ne (Ne.symm hxy), eps_not]
      ring
    have : (2:ℂ) * ∑ s : K → Bool, eps (s x) * eps (s y) = 0 := by
      rw [two_mul]; nth_rewrite 1 [key]; ring
    simpa using this

def fe {J K : Type} [AddCommGroup K] (a : K) : J × K ≃ J × K :=
  Equiv.prodCongr (Equiv.refl J) (Equiv.addRight a)

def Ug {J K : Type} [AddCommGroup K] [DecidableEq J] [DecidableEq K] (x : (K → Bool) × K) :
    Mat (J × K) :=
  Matrix.of fun p q => if q = (fe x.2).symm p then eps (x.1 q.2) else 0

lemma Ug_conj {J K : Type} [Fintype J] [Fintype K] [AddCommGroup K] [DecidableEq J] [DecidableEq K]
    (x : (K → Bool) × K) (M : Mat (J × K)) (p p' : J × K) :
    (Ug (J := J) x * M * (Ug (J := J) x)ᴴ) p p' = eps (x.1 ((fe x.2).symm p).2) * eps (x.1 ((fe x.2).symm p').2) *
      M ((fe x.2).symm p) ((fe x.2).symm p') := by
  simp [Ug, Matrix.mul_apply, Matrix.conjTranspose_apply, ite_mul, mul_ite, star_eps,
    apply_ite (starRingEnd ℂ)]
  ring

lemma Ug_unit {J K : Type} [Fintype J] [Fintype K] [AddCommGroup K] [DecidableEq J] [DecidableEq K]
    (x : (K → Bool) × K) : (Ug (J := J) x)ᴴ * Ug x = 1 ∧ Ug (J := J) x * (Ug x)ᴴ = 1 := by
  constructor
  · ext q q'
    simp only [Ug, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
    rw [← (fe x.2).sum_comp]
    simp [ite_mul, mul_ite, star_eps]
    by_cases hq : q' = q
    · subst hq; simp [eps_mul_self]
    · simp [hq, Ne.symm hq]
  · ext p p'
    simp [Ug, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, ite_mul, mul_ite,
      star_eps]
    by_cases hp : p = p'
    · subst hp; simp [eps_mul_self]
    · simp [hp]

def ptr {J K : Type} [Fintype K] (M : Mat (J × K)) : Mat J :=
  Matrix.of fun j j' => ∑ k, M (j, k) (j', k)

lemma twirl {J K : Type} [Fintype J] [Fintype K] [AddCommGroup K] [DecidableEq J] [DecidableEq K]
    [Nonempty K] (M : Mat (J × K)) :
    avgM (Ug (J := J)) (Finset.univ : Finset ((K → Bool) × K)) M =
      Matrix.kronecker (ptr M) ((((Fintype.card K : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Mat K)) := by
  ext ⟨j, k⟩ ⟨j', k'⟩
  simp only [avgM, Matrix.smul_apply, Matrix.sum_apply, Ug_conj, Finset.card_univ,
    Fintype.card_prod, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp only [fe, Equiv.prodCongr_symm, Equiv.prodCongr_apply, Equiv.refl_symm, Equiv.coe_refl,
    Equiv.addRight_symm, Prod.map, id, Equiv.coe_addRight]
  simp_rw [← Finset.sum_mul, sign_sum]
  simp only [ite_mul, zero_mul, sub_left_inj]
  by_cases hk : k = k'
  · subst hk
    simp only [if_true]
    have hsum : ∑ a : K, M (j, k + -a) (j', k + -a) = ∑ c : K, M (j, c) (j', c) := by
      exact Fintype.sum_equiv (Equiv.subLeft k) _ _ (fun a => by simp [sub_eq_add_neg])
    simp only [← Finset.mul_sum, sub_eq_add_neg, hsum]
    simp [ptr, Matrix.kronecker, Matrix.kroneckerMap_apply]
    have hc : (Fintype.card K : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have hb : (Fintype.card (K → Bool) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp
  · simp [hk, ptr, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply]


lemma D_smul2 {D : DivergenceFamily} {g : ℝ → ℝ} (hA : SixAxioms D g)
    {I : Type} [Fintype I] [DecidableEq I] (ρ σ : Mat I) (h : Domain ρ σ) (r s : ℝ)
    (hr : 0 < r) (hs : 0 < s) :
    D I ((r:ℂ) • ρ) ((s:ℂ) • σ) = D I ρ σ + D (Fin 1) ((r:ℂ) • (1 : Mat (Fin 1))) ((s:ℂ) • (1 : Mat (Fin 1))) := by
  have hτ : Domain ((r:ℂ) • (1 : Mat (Fin 1))) ((s:ℂ) • (1 : Mat (Fin 1))) :=
    ⟨Matrix.PosSemidef.one.smul (cpos hr.le), Matrix.PosSemidef.one.smul (cpos hs.le),
      smul_ne_zero (by exact_mod_cast hr.ne') one_ne_zero,
      by
        rw [dom_iff]; intro v hv
        rw [Matrix.smul_mulVec] at hv ⊢
        have : (1 : Mat (Fin 1)).mulVec v = 0 :=
          (smul_eq_zero.mp hv).resolve_left (by exact_mod_cast hs.ne')
        rw [this, smul_zero]⟩
  have e1 := hA.2.2.2.2.2.2.1 I (Fin 1) ρ σ _ _ h hτ
  let U : Matrix (I × Fin 1) I ℂ := Matrix.of fun p i => if p.1 = i then 1 else 0
  have hU1 : Uᴴ * U = 1 := by
    ext i j
    simp [U, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, Fintype.sum_prod_type]
    by_cases hij : j = i
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  have hU2 : U * Uᴴ = 1 := by
    ext ⟨i, a⟩ ⟨j, b⟩
    have hab : a = b := Subsingleton.elim _ _
    subst hab
    simp [U, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
  have e2 := hA.2.2.2.1 I (I × Fin 1) _ _ U (domain_smul h hr hs) hU1 hU2
  have k1 : ∀ (c : ℝ) (X : Mat I), U * ((c:ℂ) • X) * Uᴴ = Matrix.kronecker X ((c:ℂ) • (1 : Mat (Fin 1))) := by
    intro c X
    ext ⟨i, a⟩ ⟨j, b⟩
    have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    subst ha hb
    simp [U, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kronecker, Matrix.kroneckerMap_apply]
    ring
  rw [k1, k1] at e2
  rw [e2]
  convert e1 using 2

lemma tr_pos {I : Type} [Fintype I] {X : Mat I} (hX : X.PosSemidef) (hn : X ≠ 0) : 0 < tr X := by
  have h0 := hX.trace_nonneg
  have hne : X.trace ≠ 0 := fun h => hn (hX.trace_eq_zero_iff.1 h)
  rw [Complex.nonneg_iff] at h0
  rcases lt_or_eq_of_le h0.1 with h | h
  · exact h
  · exfalso; apply hne; apply Complex.ext
    · simp [← h]
    · simp [← h0.2]

lemma ne_zero_of_dom {I : Type} [Fintype I] [DecidableEq I] {ρ σ : Mat I} (h : Domain ρ σ) :
    σ ≠ 0 := by
  intro h0
  apply h.2.2.1
  have hd := (dom_iff _ _).1 h.2.2.2
  ext i j
  have := congrFun (hd (Pi.single j 1) (by rw [h0, Matrix.zero_mulVec])) i
  simpa [Matrix.mulVec_single] using this

lemma kraus_smul {I J : Type} [Fintype I] {m : ℕ} (F : Fin m → Matrix J I ℂ) (c : ℂ) (X : Mat I) :
    QAlgorithms.krausApply F (c • X) = c • QAlgorithms.krausApply F X := by
  simp [QAlgorithms.krausApply, Finset.smul_sum, Matrix.mul_smul, Matrix.smul_mul]

theorem dpi_density {D : DivergenceFamily} {g : ℝ → ℝ} (hA : SixAxioms D g)
    (hC : GeneralMeanConvexity D g)
    {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {m : ℕ}
    (F : Fin m → Matrix J I ℂ) (hF : ∑ k, (F k)ᴴ * F k = 1) {ρ σ : Mat I} (h : Domain ρ σ)
    (dρ : Density ρ) (dσ : Density σ) :
    D J (QAlgorithms.krausApply F ρ) (QAlgorithms.krausApply F σ) ≤ D I ρ σ := by
  obtain ⟨φ, hφ, hconv⟩ := conv_phi hA hC
  have hI : Nonempty I := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    exact h.2.2.1 (Matrix.ext fun i => isEmptyElim i)
  obtain ⟨i0⟩ := hI
  have hm : m ≠ 0 := by
    intro hm0; subst hm0
    have := congrFun (congrFun hF i0) i0
    simp at this
  haveI : NeZero m := ⟨hm⟩
  let V : Matrix (J × Fin m) I ℂ := Matrix.of fun p i => F p.2 p.1 i
  have hV : Vᴴ * V = 1 := by
    rw [← hF]
    ext i i'
    simp only [V, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.sum_apply,
      Fintype.sum_prod_type]
    rw [Finset.sum_comm]
  have hpt : ∀ X : Mat I, ptr (V * X * Vᴴ) = QAlgorithms.krausApply F X := by
    intro X
    ext j j'
    simp only [ptr, V, QAlgorithms.krausApply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply, Matrix.sum_apply]
  have e1 := D_isom hA V hV h
  have dYZ := domain_isom V hV h
  have dY : Density (V * ρ * Vᴴ) := ⟨dYZ.1, by rw [← dρ.2]; simp only [tr]; rw [trace_isom _ hV]⟩
  have dZ : Density (V * σ * Vᴴ) := ⟨dYZ.2.1, by rw [← dσ.2]; simp only [tr]; rw [trace_isom _ hV]⟩
  obtain ⟨-, -, -, hav⟩ := avg_le hA φ hconv (Ug (J := J)) (fun x => (Ug_unit x).1)
    (fun x => (Ug_unit x).2) dYZ dY dZ (Finset.univ : Finset ((Fin m → Bool) × Fin m))
    Finset.univ_nonempty
  rw [twirl, twirl, hpt, hpt] at hav
  have hc : (0:ℝ) < ((Fintype.card (Fin m) : ℝ)⁻¹) := by
    have : (0:ℝ) < Fintype.card (Fin m) := by exact_mod_cast Fintype.card_pos
    positivity
  have hτ : Domain ((((Fintype.card (Fin m) : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Mat (Fin m)))
      ((((Fintype.card (Fin m) : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Mat (Fin m))) :=
    domain_smul ⟨Matrix.PosSemidef.one, Matrix.PosSemidef.one, by
      intro h0
      have := congrFun (congrFun h0 ⟨0, Nat.pos_of_ne_zero hm⟩) ⟨0, Nat.pos_of_ne_zero hm⟩
      simp at this, le_rfl⟩ hc hc
  have dK := domain_kraus F hF h
  have e2 := hA.2.2.2.2.2.2.1 J (Fin m) _ _ _ _ dK hτ
  rw [D_self hA _ hτ, add_zero] at e2
  have : φ (D J (QAlgorithms.krausApply F ρ) (QAlgorithms.krausApply F σ)) ≤ φ (D I ρ σ) := by
    rw [← e1]
    convert hav using 2
    exact e2.symm
  exact hφ.le_iff_le.1 this

theorem conv_to_dpi {D : DivergenceFamily} {g : ℝ → ℝ} (hA : SixAxioms D g)
    (hC : GeneralMeanConvexity D g) : FamilyDPI D := by
  intro I J _ _ _ _ E hE ρ σ h
  obtain ⟨m, F, hF, hEF⟩ := hE
  rw [hEF ρ, hEF σ]
  have hr := tr_pos h.1 h.2.2.1
  have hs := tr_pos h.2.1 (ne_zero_of_dom h)
  set r := tr ρ
  set s := tr σ
  set ρ1 := (((r⁻¹ : ℝ)) : ℂ) • ρ with hρ1
  set σ1 := (((s⁻¹ : ℝ)) : ℂ) • σ with hσ1
  have h1 : Domain ρ1 σ1 := domain_smul h (inv_pos.2 hr) (inv_pos.2 hs)
  have d1 : Density ρ1 := ⟨h1.1, by rw [hρ1, tr_smul]; exact inv_mul_cancel₀ hr.ne'⟩
  have d2 : Density σ1 := ⟨h1.2.1, by rw [hσ1, tr_smul]; exact inv_mul_cancel₀ hs.ne'⟩
  have eρ : ρ = (r : ℂ) • ρ1 := by
    rw [hρ1, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hr.ne', Complex.ofReal_one, one_smul]
  have eσ : σ = (s : ℂ) • σ1 := by
    rw [hσ1, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hs.ne', Complex.ofReal_one, one_smul]
  have key := dpi_density hA hC F hF h1 d1 d2
  have a1 := D_smul2 hA ρ1 σ1 h1 r s hr hs
  have a2 := D_smul2 hA _ _ (domain_kraus F hF h1) r s hr hs
  have b1 : D I ρ σ = D I ρ1 σ1 + D (Fin 1) ((r:ℂ) • (1 : Mat (Fin 1))) ((s:ℂ) • (1 : Mat (Fin 1))) := by
    conv_lhs => rw [eρ, eσ]
    exact a1
  have b2 : D J (QAlgorithms.krausApply F ρ) (QAlgorithms.krausApply F σ) =
      D J (QAlgorithms.krausApply F ρ1) (QAlgorithms.krausApply F σ1) +
        D (Fin 1) ((r:ℂ) • (1 : Mat (Fin 1))) ((s:ℂ) • (1 : Mat (Fin 1))) := by
    have k1 : QAlgorithms.krausApply F ρ = (r:ℂ) • QAlgorithms.krausApply F ρ1 := by
      rw [← kraus_smul, ← eρ]
    have k2 : QAlgorithms.krausApply F σ = (s:ℂ) • QAlgorithms.krausApply F σ1 := by
      rw [← kraus_smul, ← eσ]
    rw [k1, k2]
    exact a2
  rw [b1, b2]
  simp only [QAlgorithms.krausApply] at key ⊢
  linarith

end X7G
end QAlgorithms.Papers.Independent.Dependency50.P35

end

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Filter Topology

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63 (Mat schatten)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

open QAlgorithms.Papers.Independent.Dependency50.P35 in
theorem solution (D : DivergenceFamily) (g : ℝ → ℝ)
    (h : SixAxioms D g) : GeneralMeanConvexity D g ↔ FamilyDPI D :=
  ⟨fun hC => X7G.conv_to_dpi h hC, fun hD => X7G.dpi_to_conv h hD⟩

end
