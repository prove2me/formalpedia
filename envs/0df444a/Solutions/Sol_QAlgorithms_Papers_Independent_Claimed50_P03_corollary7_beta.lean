-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P03.corollary7_beta
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T11:49:53.101989+00:00
-- url     : https://prove2.me/submissions/806e87a2-6a42-42b5-a68c-b6643e17006c

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03
noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace

lemma g58a_nwt_mul {I : Type*} [Fintype I] [DecidableEq I] (A B : I → Matrix Bool Bool ℂ) :
    namedWireTensor A * namedWireTensor B = namedWireTensor (fun i => A i * B i) := by
  ext x y
  simp only [Matrix.mul_apply, namedWireTensor]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.prod_mul_distrib]

lemma g58a_nwt_trace {I : Type*} [Fintype I] [DecidableEq I] (A : I → Matrix Bool Bool ℂ) :
    (namedWireTensor A).trace = ∏ i, (A i).trace := by
  simp only [Matrix.trace, Matrix.diag, namedWireTensor]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

lemma g58a_pauli_compl (a b a' b' : Bool) :
    ∑ p : Fin 4, singlePauli p a b * conj (singlePauli p a' b') =
      if a = a' ∧ b = b' then 2 else 0 := by
  rw [Fin.sum_univ_four]
  cases a <;> cases b <;> cases a' <;> cases b' <;>
    simp [singlePauli, pauliX, pauliY, pauliZ] <;> ring_nf <;> simp [Complex.I_sq] <;> norm_num

lemma g58a_pauli_herm (p : Fin 4) (a b : Bool) : star (singlePauli p a b) = singlePauli p b a := by
  fin_cases p <;> cases a <;> cases b <;> simp [singlePauli, pauliX, pauliY, pauliZ]

lemma g58a_word_apply {I : Type*} [Fintype I] [DecidableEq I] (P : I → Fin 4) (y x : I → Bool) :
    wordMatrix P y x = ∏ i, singlePauli (P i) (y i) (x i) := rfl

lemma g58a_word_compl {I : Type*} [Fintype I] [DecidableEq I] (y x y' x' : I → Bool) :
    ∑ P : I → Fin 4, wordMatrix P y x * conj (wordMatrix P y' x') =
      if y = y' ∧ x = x' then (2 : ℂ) ^ Fintype.card I else 0 := by
  simp only [g58a_word_apply, map_prod]
  simp only [← Finset.prod_mul_distrib]
  have : ∏ i, ∑ p : Fin 4, singlePauli p (y i) (x i) * conj (singlePauli p (y' i) (x' i)) =
      ∑ P : I → Fin 4, ∏ i, singlePauli (P i) (y i) (x i) * conj (singlePauli (P i) (y' i) (x' i)) := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rw [← this]
  simp only [g58a_pauli_compl]
  by_cases h : y = y' ∧ x = x'
  · obtain ⟨rfl, rfl⟩ := h; simp
  · rw [if_neg h]
    have : ∃ i, ¬ (y i = y' i ∧ x i = x' i) := by
      by_contra hc; push Not at hc
      exact h ⟨funext fun i => (hc i).1, funext fun i => (hc i).2⟩
    obtain ⟨i, hi⟩ := this
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

lemma g58a_word_herm {I : Type*} [Fintype I] [DecidableEq I] (P : I → Fin 4) : (wordMatrix P)ᴴ = wordMatrix P := by
  ext x y
  rw [Matrix.conjTranspose_apply, g58a_word_apply, g58a_word_apply]
  rw [show star (∏ i, singlePauli (P i) (y i) (x i)) = starRingEnd ℂ (∏ i, singlePauli (P i) (y i) (x i))
    from rfl, map_prod]
  exact Finset.prod_congr rfl fun i _ => g58a_pauli_herm _ _ _

lemma g58a_trP (p : Fin 4) : (singlePauli p).trace = if p = 0 then 2 else 0 := by
  fin_cases p <;> simp [singlePauli, pauliX, pauliY, pauliZ, Matrix.trace, Fintype.sum_bool] <;> norm_num

lemma g58a_signsum (m : ℕ) : ∑ b : Bool, ((rademacherValue b : ℝ) : ℂ) ^ m =
    if Even m then 2 else 0 := by
  simp only [Fintype.sum_bool, rademacherValue, if_true, Bool.false_eq_true, if_false]
  split_ifs with h
  · rw [Complex.ofReal_neg, Complex.ofReal_one, h.neg_one_pow]; norm_num
  · rw [Complex.ofReal_neg, Complex.ofReal_one, (Nat.not_even_iff_odd.mp h).neg_one_pow]; norm_num

lemma g58a_count {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (hc : Fintype.card α = Fintype.card β)
    (F : α → β) : (∀ b, Odd (Finset.univ.filter fun a => F a = b).card) ↔ Function.Bijective F := by
  constructor
  · intro h
    have hs : Function.Surjective F := by
      intro b
      obtain ⟨a, ha⟩ := Finset.card_pos.mp (h b).pos
      exact ⟨a, (Finset.mem_filter.mp ha).2⟩
    exact (Fintype.bijective_iff_surjective_and_card F).mpr ⟨hs, hc⟩
  · intro hb b
    obtain ⟨a, rfl⟩ := hb.2 b
    have : (Finset.univ.filter fun a' => F a' = F a) = {a} := by
      ext a'; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h => hb.1 h, fun h => h ▸ rfl⟩
    rw [this, Finset.card_singleton]; exact odd_one

lemma g58a_sign_orth {k : ℕ} {α : Type*} [Fintype α] (hc : Fintype.card α = k) (F : α → Fin k) :
    ∑ σ : Fin k → Bool, (∏ s, ((rademacherValue (σ s) : ℝ) : ℂ)) *
      ∏ a, ((rademacherValue (σ (F a)) : ℝ) : ℂ) =
      if Function.Bijective F then (2 : ℂ) ^ k else 0 := by
  classical
  have h1 : ∀ σ : Fin k → Bool, (∏ s, ((rademacherValue (σ s) : ℝ) : ℂ)) *
      ∏ a, ((rademacherValue (σ (F a)) : ℝ) : ℂ) =
      ∏ s, ((rademacherValue (σ s) : ℝ) : ℂ) ^ ((Finset.univ.filter fun a => F a = s).card + 1) := by
    intro σ
    rw [← Finset.prod_fiberwise Finset.univ F (fun a => ((rademacherValue (σ (F a)) : ℝ) : ℂ)),
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [Finset.prod_congr rfl (g := fun _ => ((rademacherValue (σ s) : ℝ) : ℂ))
      (fun a ha => by rw [(Finset.mem_filter.mp ha).2]), Finset.prod_const, pow_succ]
    ring
  simp only [h1]
  have hp := Finset.prod_univ_sum (fun _ : Fin k => (Finset.univ : Finset Bool))
    (fun s b => ((rademacherValue b : ℝ) : ℂ) ^ ((Finset.univ.filter fun a => F a = s).card + 1))
  rw [Fintype.piFinset_univ] at hp
  rw [← hp]
  simp only [g58a_signsum]
  have hcount := g58a_count (by simpa using hc) F
  by_cases hb : Function.Bijective F
  · have h := hcount.mpr hb
    rw [if_pos hb, Finset.prod_congr rfl (g := fun _ => (2 : ℂ)) (fun s _ => by
      rw [if_pos (by rw [Nat.even_add_one, Nat.not_even_iff_odd]; exact h s)])]
    simp
  · rw [if_neg hb]
    have h : ¬ ∀ s, Odd (Finset.univ.filter fun a => F a = s).card := fun h => hb (hcount.mp h)
    push Not at h
    obtain ⟨s, hs⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_univ s)
    rw [if_neg]
    rw [Nat.even_add_one, not_not]
    exact Nat.not_odd_iff_even.mp hs

lemma g58a_path_wire (p : Fin 4) {k : ℕ} (c : ℂ) (rs : Fin k → ℝ) (ρ : Fin k → Matrix Bool Bool ℂ)
    (htr : ∀ s, (ρ s).trace = 1) :
    (singlePauli p * ((1 / 2 : ℂ) • (1 : Matrix Bool Bool ℂ) + (c : ℂ) • ∑ s, (rs s : ℂ) •
      (ρ s - (1 / 2 : ℂ) • (1 : Matrix Bool Bool ℂ)))).trace =
      if p = 0 then 1 else (c : ℂ) * ∑ s, (rs s : ℂ) * (singlePauli p * ρ s).trace := by
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_sum, Matrix.mul_sub, Matrix.mul_one,
    Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sum, Matrix.trace_sub, g58a_trP, smul_eq_mul]
  split_ifs with h
  · subst h
    simp only [singlePauli, if_true, Matrix.one_mul, htr]
    norm_num
  · simp

lemma g58a_lhs {I : Type*} [Fintype I] [DecidableEq I] {k : ℕ} (P : I → Fin 4) (rho : Fin k → I → Matrix Bool Bool ℂ)
    (htr : ∀ s i, (rho s i).trace = 1) (e : Fin k → I) :
    (namedWireTensor (fun si : Fin k × I => if e si.1 = si.2 then singlePauli (P si.2) else 1) *
      namedWireTensor (fun si : Fin k × I => rho si.1 si.2)).trace =
      ∏ s, (singlePauli (P (e s)) * rho s (e s)).trace := by
  rw [g58a_nwt_mul, g58a_nwt_trace, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun s _ => ?_
  have : ∀ i, ((if e s = i then singlePauli (P i) else 1) * rho s i).trace =
      if e s = i then (singlePauli (P i) * rho s i).trace else 1 := by
    intro i; split_ifs <;> simp [htr]
  simp only [this]
  rw [Finset.prod_ite_eq]; simp

lemma g58a_rhs {I : Type*} [Fintype I] [DecidableEq I] {k : ℕ} (P : I → Fin 4) (hw : pauliWeight P = k)
    (rho : Fin k → I → Matrix Bool Bool ℂ) (htr : ∀ s i, (rho s i).trace = 1) (t : ℝ)
    (σ : Fin k → Bool) :
    (wordMatrix P * productPath t rho σ).trace =
      ((t : ℂ) / ((k : ℝ) : ℂ)) ^ k * ∑ F : (wordSupport P) → Fin k,
        ∏ x : (wordSupport P), ((rademacherValue (σ (F x)) : ℝ) : ℂ) *
          (singlePauli (P x) * rho (F x) x).trace := by
  unfold wordMatrix productPath
  rw [g58a_nwt_mul, g58a_nwt_trace]
  rw [Finset.prod_congr rfl (fun i _ => g58a_path_wire (P i) ((t : ℂ) / ((k : ℝ) : ℂ)) (fun s => rademacherValue (σ s)) (fun s => rho s i) (fun s => htr s i))]
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul]
  have hs : (Finset.univ.filter fun i => ¬ P i = 0) = wordSupport P := rfl
  rw [hs, ← Finset.prod_coe_sort, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_coe]
  have hk : (wordSupport P).card = k := hw
  rw [hk]
  congr 1
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

lemma g58a_reindex {I : Type*} [Fintype I] [DecidableEq I] {k : ℕ} (P : I → Fin 4)
    (B : Fin k → I → ℂ) :
    ∑ e ∈ Finset.univ.filter (fun e : Fin k → I =>
        Function.Injective e ∧ Finset.univ.image e = wordSupport P), ∏ s, B s (e s) =
      ∑ F ∈ Finset.univ.filter (fun F : (wordSupport P) → Fin k => Function.Bijective F),
        ∏ x : (wordSupport P), B (F x) x := by
  classical
  have memS : ∀ e : Fin k → I, Finset.univ.image e = wordSupport P → ∀ s, e s ∈ wordSupport P :=
    fun e he s => he ▸ Finset.mem_image_of_mem e (Finset.mem_univ s)
  have h1 : ∑ e ∈ Finset.univ.filter (fun e : Fin k → I =>
        Function.Injective e ∧ Finset.univ.image e = wordSupport P), ∏ s, B s (e s) =
      ∑ E : Fin k ≃ (wordSupport P), ∏ s, B s (E s).1 := by
    refine Finset.sum_bij' (fun e he => Equiv.ofBijective (fun s => (⟨e s, memS e
        (Finset.mem_filter.mp he).2.2 s⟩ : wordSupport P)) ⟨fun a b hab => (Finset.mem_filter.mp he).2.1
          (congrArg Subtype.val hab), fun x => by
            have hx : x.1 ∈ Finset.univ.image e := by
              rw [(Finset.mem_filter.mp he).2.2]; exact x.2
            obtain ⟨s, -, hs⟩ := Finset.mem_image.mp hx
            exact ⟨s, Subtype.ext hs⟩⟩)
      (fun E _ => fun s => (E s).1) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_ ?_
    · intro E _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨fun a b hab => E.injective (Subtype.ext hab), ?_⟩
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨s, rfl⟩; exact (E s).2
      · intro hx; exact ⟨E.symm ⟨x, hx⟩, by simp⟩
    · intro e he; rfl
    · intro E _; ext s; rfl
    · intro e he; rfl
  have h2 : ∑ F ∈ Finset.univ.filter (fun F : (wordSupport P) → Fin k => Function.Bijective F),
        ∏ x : (wordSupport P), B (F x) x =
      ∑ E : (wordSupport P) ≃ Fin k, ∏ x : (wordSupport P), B (E x) x := by
    refine Finset.sum_bij' (fun F hF => Equiv.ofBijective F (Finset.mem_filter.mp hF).2)
      (fun E _ => ⇑E) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_ ?_
    · intro E _; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact E.bijective
    · intro F _; rfl
    · intro E _; ext x; rfl
    · intro F _; rfl
  rw [h1, h2]
  refine Finset.sum_bij' (fun E _ => E.symm) (fun E _ => E.symm) (fun _ _ => Finset.mem_univ _)
    (fun _ _ => Finset.mem_univ _) (fun E _ => E.symm_symm) (fun E _ => E.symm_symm) ?_
  intro E _
  exact Fintype.prod_equiv E _ _ (fun s => by simp)

lemma g58a_perword {I : Type*} [Fintype I] [DecidableEq I] {k : ℕ} (P : I → Fin 4) (hw : pauliWeight P = k)
    (rho : Fin k → I → Matrix Bool Bool ℂ) (htr : ∀ s i, (rho s i).trace = 1) (t : ℝ) :
    (t : ℂ) ^ k * ∑ e ∈ Finset.univ.filter (fun e : Fin k → I =>
        Function.Injective e ∧ Finset.univ.image e = wordSupport P),
      (namedWireTensor (fun si : Fin k × I => if e si.1 = si.2 then singlePauli (P si.2) else 1) *
        namedWireTensor (fun si : Fin k × I => rho si.1 si.2)).trace =
    (k : ℂ) ^ k * ((∑ σ : Fin k → Bool, (∏ s, ((rademacherValue (σ s) : ℝ) : ℂ)) *
      (wordMatrix P * productPath t rho σ).trace) / 2 ^ k) := by
  classical
  set B : Fin k → I → ℂ := fun s i => (singlePauli (P i) * rho s i).trace with hB
  simp only [g58a_lhs P rho htr]
  have hre := g58a_reindex P B
  simp only [hB] at hre
  rw [hre]
  simp only [g58a_rhs P hw rho htr t]
  have hcard : Fintype.card (wordSupport P) = k := by rw [Fintype.card_coe]; exact hw
  have e1 : ∑ σ : Fin k → Bool, (∏ s, ((rademacherValue (σ s) : ℝ) : ℂ)) *
      (((t : ℂ) / ((k : ℝ) : ℂ)) ^ k * ∑ F : (wordSupport P) → Fin k,
        ∏ x : (wordSupport P), ((rademacherValue (σ (F x)) : ℝ) : ℂ) * B (F x) x) =
      ((t : ℂ) / ((k : ℝ) : ℂ)) ^ k * ∑ F : (wordSupport P) → Fin k, (∏ x : (wordSupport P), B (F x) x) *
        ∑ σ : Fin k → Bool, (∏ s, ((rademacherValue (σ s) : ℝ) : ℂ)) *
          ∏ x : (wordSupport P), ((rademacherValue (σ (F x)) : ℝ) : ℂ) := by
    simp only [Finset.prod_mul_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun F _ => Finset.sum_congr rfl fun σ _ => by ring
  simp only [hB] at e1
  rw [e1]
  simp only [g58a_sign_orth hcard, mul_ite, mul_zero]
  rw [← Finset.sum_filter, ← Finset.sum_mul]
  have : ((k : ℝ) : ℂ) = (k : ℂ) := by push_cast; rfl
  rw [this, div_pow]
  have hkk : (k : ℂ) ^ k ≠ 0 := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp
    · exact pow_ne_zero _ (by exact_mod_cast h.ne')
  field_simp

lemma g58a_coef_eq {I : Type*} [Fintype I] [DecidableEq I] (H : Matrix ((I → Bool)) ((I → Bool)) ℂ) (hH : H.IsHermitian)
    (P : I → Fin 4) :
    ((coefficient H P : ℝ) : ℂ) = (wordMatrix P * H).trace / 2 ^ Fintype.card I := by
  have hreal : ((wordMatrix P * H).trace.re : ℂ) = (wordMatrix P * H).trace := by
    have : star (wordMatrix P * H).trace = (wordMatrix P * H).trace := by
      rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hH.eq, g58a_word_herm,
        Matrix.trace_mul_comm]
    exact Complex.conj_eq_iff_re.mp this
  rw [← hreal]
  unfold coefficient
  push_cast
  congr
  all_goals exact Subsingleton.elim _ _

lemma g58a_expand {I : Type*} [Fintype I] [DecidableEq I] (H : Matrix ((I → Bool)) ((I → Bool)) ℂ) (hH : H.IsHermitian) :
    H = ∑ P : I → Fin 4, ((coefficient H P : ℝ) : ℂ) • wordMatrix P := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, g58a_coef_eq H hH]
  have hW : ∀ P : I → Fin 4, wordMatrix P a b = conj (wordMatrix P b a) := by
    intro P
    have := congrFun (congrFun (g58a_word_herm P) a) b
    rw [Matrix.conjTranspose_apply] at this
    rw [← this]; rfl
  simp only [hW, Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_div, Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ y : (I → Bool), ∑ P : I → Fin 4, ∑ x, wordMatrix P y x * H x y / 2 ^ Fintype.card I *
      conj (wordMatrix P b a) = ∑ x, H x y / 2 ^ Fintype.card I * (∑ P : I → Fin 4,
        wordMatrix P y x * conj (wordMatrix P b a)) := by
    intro y
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun P _ => by ring
  simp only [this, g58a_word_compl]
  rw [Finset.sum_eq_single b, Finset.sum_eq_single a]
  · simp
  · intro x _ hx; simp [hx]
  · simp
  · intro y _ hy; simp [hy]
  · simp

theorem g58a_pol_gen {I : Type*} [Fintype I] [DecidableEq I] (k : ℕ)
    (O : (Matrix (I → Bool) (I → Bool) ℂ)) (hO : O.IsHermitian) (hhom : IsHomogeneous k O)
    (rho : Fin k → I → Matrix Bool Bool ℂ)
    (htr : ∀ s i, (rho s i).trace = 1) (t : ℝ) :
    t ^ k * effectProb (polarization k O) (namedWireTensor (fun si : Fin k × I => rho si.1 si.2)) =
      (k : ℝ) ^ k / (Nat.factorial k : ℝ) * signAverage k (fun sigma =>
        (∏ s, rademacherValue (sigma s)) * effectProb O (productPath t rho sigma)) := by
  set X := namedWireTensor (fun si : Fin k × I => rho si.1 si.2) with hX
  set L : (I → Fin 4) → ℝ := fun P => (∑ e ∈ Finset.univ.filter (fun e : Fin k → I =>
        Function.Injective e ∧ Finset.univ.image e = wordSupport P),
      (namedWireTensor (fun si : Fin k × I => if e si.1 = si.2 then singlePauli (P si.2) else 1) *
        X).trace).re with hL
  have hLHS : effectProb (polarization k O) X =
      ∑ P : I → Fin 4, coefficient O P / (Nat.factorial k : ℝ) * L P := by
    unfold effectProb polarization
    rw [Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
      ← Complex.ofReal_div, Complex.re_ofReal_mul, Finset.sum_mul, Matrix.trace_sum]
  have hE : ∀ Y, effectProb O Y = ∑ P : I → Fin 4, coefficient O P * (wordMatrix P * Y).trace.re := by
    intro Y
    conv_lhs => rw [g58a_expand O hO]
    unfold effectProb
    rw [Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  set R : (I → Fin 4) → ℝ := fun P => (∑ σ : Fin k → Bool, (∏ s, rademacherValue (σ s)) *
      (wordMatrix P * productPath t rho σ).trace.re) / 2 ^ k with hR
  have hRHS : signAverage k (fun sigma =>
        (∏ s, rademacherValue (sigma s)) * effectProb O (productPath t rho sigma)) =
      ∑ P : I → Fin 4, coefficient O P * R P := by
    unfold signAverage
    simp only [hE, hR, Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_div]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [mul_div_assoc', Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun σ _ => by ring
  have key : ∀ P, coefficient O P ≠ 0 → t ^ k * L P = (k : ℝ) ^ k * R P := by
    intro P hc
    have hw : pauliWeight P = k := by
      by_contra h; exact hc (hhom P h)
    have := congrArg Complex.re (g58a_perword P hw rho htr t)
    rw [show (t : ℂ) ^ k = ((t ^ k : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul,
      show (k : ℂ) ^ k = (((k : ℝ) ^ k : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul,
      show (2 : ℂ) ^ k = (((2 : ℝ) ^ k : ℝ) : ℂ) by push_cast; rfl, Complex.div_ofReal_re,
      Complex.re_sum] at this
    simp only [← Complex.ofReal_prod, Complex.re_sum, Complex.re_ofReal_mul] at this
    simp only [hL, hR, Complex.re_sum]
    exact this
  rw [hLHS, hRHS, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  by_cases hc : coefficient O P = 0
  · simp [hc]
  · have := key P hc
    linear_combination (coefficient O P / (Nat.factorial k : ℝ)) * this

lemma g58a_pp (a b : Fin 4) : (singlePauli a * singlePauli b).trace = if a = b then 2 else 0 := by
  fin_cases a <;> fin_cases b <;>
    simp [singlePauli, pauliX, pauliY, pauliZ, Matrix.trace, Fintype.sum_bool, Matrix.mul_apply] <;>
    norm_num [Complex.I_sq]

lemma g58a_orth {I : Type*} [Fintype I] [DecidableEq I] (A B : I → Fin 4) (h : A ≠ B) :
    (wordMatrix A * wordMatrix B).trace = 0 := by
  unfold wordMatrix
  rw [g58a_nwt_mul, g58a_nwt_trace]
  obtain ⟨j, hj⟩ := Function.ne_iff.mp h
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [g58a_pp, if_neg hj])

lemma g58a_pure_trace (ρ : Matrix Bool Bool ℂ) (h : IsPureQubit ρ) : ρ.trace = 1 := by
  obtain ⟨ψ, hψ, rfl⟩ := h
  have h1 : ‖ψ‖ = 1 := hψ
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h1
  simp only [Matrix.trace, Matrix.diag, pureDensity, Matrix.of_apply, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]
  exact_mod_cast h1

theorem solution (n k de q : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hde : 1 ≤ de) (hden : de ≤ n) (ce : ℝ) (hce : 1 ≤ ce)
    (H : (Matrix (Qubits n) (Qubits n) ℂ)) (hH : H.IsHermitian) (hloc : IsLocal k H)
    (hexp : HasExpansion H ce de)
    (hq : bestDegree H k (expansionExponent de) = q + 1)
    (rho : Fin q → Fin n → Matrix Bool Bool ℂ) (hrho : ∀ s j, IsPureQubit (rho s j))
    (i : Fin n) (p : Fin 3) :
    effectProb (polarization q (deletedSlice (q + 1) H i p))
      (namedWireTensor (fun sj : Fin q × {j : Fin n // j ≠ i} => rho sj.1 sj.2.val)) =
      (q : ℝ) ^ q / (Nat.factorial q : ℝ) * localBeta H rho i p := by
  set D := deletedSlice (q + 1) H i p with hD
  have hDdef : D = ∑ P ∈ Finset.univ.filter (fun P : (Fin n → Fin 4) =>
      pauliWeight P = q + 1 ∧ (P i).val = p.val + 1),
      ((coefficient H P : ℝ) : ℂ) • wordMatrix (fun j : {j : Fin n // j ≠ i} => P j.val) := rfl
  have hDH : D.IsHermitian := by
    rw [hDdef]
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [Matrix.conjTranspose_smul, g58a_word_herm]
    congr 1
    simp
  have hwt : ∀ P : Fin n → Fin 4, pauliWeight P = q + 1 → P i ≠ 0 →
      pauliWeight (fun j : {j : Fin n // j ≠ i} => P j.val) = q := by
    intro P hP hi
    have : (wordSupport (fun j : {j : Fin n // j ≠ i} => P j.val)).map
        (Function.Embedding.subtype _) = (wordSupport P).erase i := by
      ext x
      simp only [Finset.mem_map, wordSupport, Finset.mem_filter, Finset.mem_univ, true_and,
        Function.Embedding.coe_subtype, Finset.mem_erase]
      constructor
      · rintro ⟨j, hj, rfl⟩; exact ⟨j.2, hj⟩
      · rintro ⟨hx, hx'⟩; exact ⟨⟨x, hx⟩, hx', rfl⟩
    have h2 := congrArg Finset.card this
    rw [Finset.card_map, Finset.card_erase_of_mem (by simp [wordSupport, hi])] at h2
    unfold pauliWeight at hP ⊢
    omega
  have hhom : IsHomogeneous q D := by
    intro P' hP'
    have h0 : (wordMatrix P' * D).trace = 0 := by
      rw [hDdef, Matrix.mul_sum, Matrix.trace_sum]
      refine Finset.sum_eq_zero fun P hP => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hP
      rw [Matrix.mul_smul, Matrix.trace_smul, g58a_orth, smul_zero]
      intro h
      apply hP'
      rw [h]
      exact hwt P hP.1 (by intro h0; have := hP.2; rw [h0] at this; simp at this)
    have := g58a_coef_eq D hDH P'
    rw [h0, zero_div] at this
    exact_mod_cast this
  have htr : ∀ s (j : {j : Fin n // j ≠ i}), (rho s j.val).trace = 1 :=
    fun s j => g58a_pure_trace _ (hrho s j.val)
  have := g58a_pol_gen q D hDH hhom (fun s (j : {j : Fin n // j ≠ i}) => rho s j.val) htr 1
  rw [one_pow, one_mul] at this
  rw [this]
  rfl

end
