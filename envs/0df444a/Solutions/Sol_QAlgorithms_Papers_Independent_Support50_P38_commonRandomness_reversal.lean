-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P38.commonRandomness_reversal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T04:20:44.476984+00:00
-- url     : https://prove2.me/submissions/d796169f-3d57-4cd3-9438-c4710087792d

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P38

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Support50.P38

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon labelInformation)

attribute [local instance] Classical.propDecidable

/-! ### Basic lemmas -/

lemma crr_wordMass_nonneg {A : Type} [Fintype A] {n : ℕ} {p : A → ℝ} (hp : IsLaw p) (x : SourceWord A n) :
    0 ≤ wordMass p x :=
  Finset.prod_nonneg fun i _ => hp.1 (x i)

lemma crr_wordMass_sum {A : Type} [Fintype A] {n : ℕ} {p : A → ℝ} (hp : IsLaw p) :
    ∑ x : SourceWord A n, wordMass p x = 1 := by
  unfold wordMass
  rw [← Fintype.prod_sum]
  simp [hp.2]

lemma crr_wordChannel_law {A B : Type} [Fintype B] {n : ℕ} {w : A → B → ℝ}
    (hw : IsStochastic w) (x : SourceWord A n) : IsLaw (wordChannel w x) := by
  constructor
  · intro y
    exact Finset.prod_nonneg fun i _ => (hw (x i)).1 (y i)
  · unfold wordChannel
    rw [← Fintype.prod_sum]
    simp [fun a => (hw a).2]

lemma crr_tv_triangle {X : Type} [Fintype X] (p q r : X → ℝ) : tv p r ≤ tv p q + tv q r := by
  unfold tv
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  have := abs_sub_le (p x) (q x) (r x)
  linarith

/-- Mixture total-variation bound. -/
lemma crr_tv_mix {X M : Type} [Fintype X] [Fintype M] (q q' : M → ℝ) (f : M → X → ℝ)
    (hf : ∀ m, IsLaw (f m)) :
    tv (fun z => ∑ m, q m * f m z) (fun z => ∑ m, q' m * f m z) ≤ (∑ m, |q m - q' m|) / 2 := by
  unfold tv
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc ∑ z, |∑ m, q m * f m z - ∑ m, q' m * f m z|
      = ∑ z, |∑ m, (q m - q' m) * f m z| := by
        congr 1; ext z; rw [← Finset.sum_sub_distrib]; congr 1; apply Finset.sum_congr rfl; intro m _; ring
    _ ≤ ∑ z, ∑ m, |q m - q' m| * f m z := by
        apply Finset.sum_le_sum; intro z _
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        apply Finset.sum_le_sum; intro m _
        rw [abs_mul, abs_of_nonneg ((hf m).1 z)]
    _ = ∑ m, |q m - q' m| * ∑ z, f m z := by
        rw [Finset.sum_comm]; congr 1; ext m; rw [Finset.mul_sum]
    _ = ∑ m, |q m - q' m| := by simp [fun m => (hf m).2]

/-- The code set for `minimumSize` is nonempty: exact transmission of the label. -/
lemma crr_exists_code {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (p : A → ℝ) (w : A → B → ℝ) (hw : IsStochastic w) (n : ℕ) (error : ℝ) (he : 0 ≤ error) :
    ∃ c : DistributionCompressionCode A B n, sourceAverageBlockError p w c.output ≤ error := by
  classical
  let e := Fintype.equivFin (SourceWord A n)
  refine ⟨⟨Fintype.card (SourceWord A n), Fintype.card_pos,
    fun x m => if m = e x then 1 else 0, ?_, fun m y => wordChannel w (e.symm m) y, ?_⟩, ?_⟩
  · intro x; constructor
    · intro m; dsimp only; split_ifs <;> norm_num
    · simp
  · intro m; exact crr_wordChannel_law hw _
  · have : ∀ x y, (∑ m, (if m = e x then (1:ℝ) else 0) * wordChannel w (e.symm m) y) =
        wordChannel w x y := by
      intro x y; simp
    unfold sourceAverageBlockError DistributionCompressionCode.output
    simp only [this]
    simp [tv, he]

lemma crr_minimumSize_mem {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (p : A → ℝ) (w : A → B → ℝ) (hw : IsStochastic w) (n : ℕ) (error : ℝ) (he : 0 ≤ error) :
    ∃ c : DistributionCompressionCode A B n, c.size = minimumSize p w n error ∧
      sourceAverageBlockError p w c.output ≤ error := by
  obtain ⟨c, hc⟩ := crr_exists_code p w hw n error he
  have hne : {m | ∃ c : DistributionCompressionCode A B n, c.size = m ∧
      sourceAverageBlockError p w c.output ≤ error}.Nonempty := ⟨c.size, c, rfl, hc⟩
  obtain ⟨c', hc'⟩ := Nat.sInf_mem hne
  exact ⟨c', hc'⟩

lemma crr_minimumSize_pos {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (p : A → ℝ) (w : A → B → ℝ) (hw : IsStochastic w) (n : ℕ) (error : ℝ) (he : 0 ≤ error) :
    0 < minimumSize p w n error := by
  obtain ⟨c, hc, _⟩ := crr_minimumSize_mem p w hw n error he
  rw [← hc]; exact c.size_pos

/-! ### Transport of Question 4 to arbitrary finite alphabets -/

lemma crr_shannon_comp {J B : Type} [Fintype J] [Fintype B] (σ : J ≃ B) (g : B → ℝ) :
    shannon (fun j => g (σ j)) = shannon g := by
  unfold shannon
  congr 1
  exact Equiv.sum_comp σ (fun b => g b * Real.logb 2 (g b))

lemma crr_info_transport {A B : Type} [Fintype A] [Fintype B]
    (p : A → ℝ) (w : A → B → ℝ) (e : A ≃ Fin (Fintype.card A)) (f : B ≃ Fin (Fintype.card B)) :
    sourceInformationBits (fun i => p (e.symm i)) (fun i j => w (e.symm i) (f.symm j)) =
      sourceInformationBits p w := by
  unfold sourceInformationBits sourceConditionalEntropyBits
  have h1 : sourceOutputMarginal (fun i => p (e.symm i)) (fun i j => w (e.symm i) (f.symm j)) =
      fun j => sourceOutputMarginal p w (f.symm j) := by
    funext j
    unfold sourceOutputMarginal
    exact Equiv.sum_comp e.symm (fun a => p a * w a (f.symm j))
  rw [h1, crr_shannon_comp f.symm]
  congr 1
  have h2 : ∀ a, shannon (fun j => w a (f.symm j)) = shannon (w a) :=
    fun a => crr_shannon_comp f.symm (w a)
  simp only [h2]
  exact Equiv.sum_comp e.symm (fun a => p a * shannon (w a))

lemma crr_minimumSize_transport {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (p : A → ℝ) (w : A → B → ℝ) (hp : IsLaw p) (hw : IsStochastic w)
    (e : A ≃ Fin (Fintype.card A)) (f : B ≃ Fin (Fintype.card B))
    (n : ℕ) (error : ℝ) (he : 0 ≤ error) :
    minimumSize p w n error ≤
      minimumSize (fun i => p (e.symm i)) (fun i j => w (e.symm i) (f.symm j)) n error := by
  classical
  set p' : Fin (Fintype.card A) → ℝ := fun i => p (e.symm i) with hp'
  set w' : Fin (Fintype.card A) → Fin (Fintype.card B) → ℝ := fun i j => w (e.symm i) (f.symm j)
    with hw'
  have hw'law : IsStochastic w' := fun i => by
    constructor
    · intro j; exact (hw _).1 _
    · exact Equiv.sum_comp f.symm (w (e.symm i)) |>.trans (hw _).2
  haveI : Nonempty (Fin (Fintype.card A)) := ⟨e (Classical.arbitrary A)⟩
  haveI : Nonempty (Fin (Fintype.card B)) := ⟨f (Classical.arbitrary B)⟩
  obtain ⟨c', hc'size, hc'err⟩ := crr_minimumSize_mem p' w' hw'law n error he
  let E : SourceWord A n ≃ SourceWord (Fin (Fintype.card A)) n := Equiv.piCongrRight fun _ => e
  let F : SourceWord B n ≃ SourceWord (Fin (Fintype.card B)) n := Equiv.piCongrRight fun _ => f
  have hE : ∀ x : SourceWord A n, E x = fun i => e (x i) := fun x => rfl
  have hF : ∀ y : SourceWord B n, F y = fun i => f (y i) := fun y => rfl
  let c : DistributionCompressionCode A B n :=
    { size := c'.size
      size_pos := c'.size_pos
      enc := fun x m => c'.enc (E x) m
      enc_law := fun x => c'.enc_law (E x)
      dec := fun m y => c'.dec m (F y)
      dec_law := fun m => by
        constructor
        · intro y; exact (c'.dec_law m).1 _
        · exact (Equiv.sum_comp F (c'.dec m)).trans (c'.dec_law m).2 }
  have hmass : ∀ x : SourceWord A n, wordMass p x = wordMass p' (E x) := by
    intro x; simp [wordMass, hp', hE]
  have hchan : ∀ (x : SourceWord A n) (y : SourceWord B n),
      wordChannel w x y = wordChannel w' (E x) (F y) := by
    intro x y; simp [wordChannel, hw', hE, hF]
  have hout : ∀ (x : SourceWord A n) (y : SourceWord B n),
      c.output x y = c'.output (E x) (F y) := fun x y => rfl
  have htv : ∀ x : SourceWord A n,
      tv (wordChannel w x) (c.output x) = tv (wordChannel w' (E x)) (c'.output (E x)) := by
    intro x
    unfold tv
    congr 1
    rw [← Equiv.sum_comp F]
    apply Finset.sum_congr rfl
    intro y _
    rw [hchan, hout]
  have herr : sourceAverageBlockError p w c.output = sourceAverageBlockError p' w' c'.output := by
    unfold sourceAverageBlockError
    rw [← Equiv.sum_comp E]
    apply Finset.sum_congr rfl
    intro x _
    rw [hmass, htv]
  have hmem : c.size ∈ {m | ∃ c : DistributionCompressionCode A B n, c.size = m ∧
      sourceAverageBlockError p w c.output ≤ error} := ⟨c, rfl, by rw [herr]; exact hc'err⟩
  have := Nat.sInf_le hmem
  unfold minimumSize
  calc sInf {m | ∃ c : DistributionCompressionCode A B n, c.size = m ∧
      sourceAverageBlockError p w c.output ≤ error} ≤ c.size := this
    _ = c'.size := rfl
    _ = _ := hc'size

lemma crr_sizeRate_bound {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (hq : QuestionFour) (p : A → ℝ) (w : A → B → ℝ) (hp : IsLaw p) (hw : IsStochastic w)
    (error : ℝ) (he : 0 < error) (he1 : error < 1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, Real.logb 2 (minimumSize p w (n + 1) error : ℝ) ≤
      (n + 1 : ℝ) * (sourceInformationBits p w + δ) := by
  classical
  let e := Fintype.equivFin A
  let f := Fintype.equivFin B
  set p' : Fin (Fintype.card A) → ℝ := fun i => p (e.symm i) with hp'
  set w' : Fin (Fintype.card A) → Fin (Fintype.card B) → ℝ := fun i j => w (e.symm i) (f.symm j)
    with hw'
  have hp'law : IsLaw p' := by
    constructor
    · intro i; exact hp.1 _
    · exact (Equiv.sum_comp e.symm p).trans hp.2
  have hw'law : IsStochastic w' := fun i => by
    constructor
    · intro j; exact (hw _).1 _
    · exact Equiv.sum_comp f.symm (w (e.symm i)) |>.trans (hw _).2
  have hT := hq (Fintype.card A) (Fintype.card B) Fintype.card_pos Fintype.card_pos p' w'
    hp'law hw'law error he he1
  have hI : sourceInformationBits p' w' = sourceInformationBits p w := crr_info_transport p w e f
  rw [hI] at hT
  have hev := (tendsto_order.1 hT).2 (sourceInformationBits p w + δ) (by linarith)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  unfold sizeRate at h1
  have hpos : (0 : ℝ) < (n + 1 : ℝ) := by positivity
  have h2 : Real.logb 2 (minimumSize p' w' (n + 1) error : ℝ) ≤
      (n + 1 : ℝ) * (sourceInformationBits p w + δ) := by
    rw [div_lt_iff₀ hpos] at h1
    linarith
  refine le_trans ?_ h2
  apply Real.logb_le_logb_of_le (by norm_num)
  · exact_mod_cast crr_minimumSize_pos p w hw (n + 1) error he.le
  · exact_mod_cast crr_minimumSize_transport p w hp hw e f (n + 1) error he.le

/-! ### The reversal construction from one code -/

lemma crr_construct {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (p : A → ℝ) (w : A → B → ℝ) (hp : IsLaw p) {n : ℕ}
    (c : DistributionCompressionCode A B n) (error : ℝ) (he : 0 < error)
    (hc : sourceAverageBlockError p w c.output ≤ error / 2) (L : ℕ) (hL : 2 / error ≤ L) :
    ∃ seeds : ℕ, 0 < seeds ∧ (seeds : ℝ) ≤ c.size * (L + 1) ∧
      ∃ (a : Fin seeds → SourceWord A n → ℝ) (b : Fin seeds → SourceWord B n → ℝ),
        IsStochastic a ∧ IsStochastic b ∧ tv (jointWordLaw p w) (generatedPairs a b) ≤ error := by
  classical
  set M := c.size with hM
  have hMpos : 0 < M := c.size_pos
  have hLpos : (0 : ℝ) < L := lt_of_lt_of_le (by positivity) hL
  set q : Fin M → ℝ := c.messageLaw p with hqdef
  have hq0 : ∀ m, 0 ≤ q m := fun m =>
    Finset.sum_nonneg fun x _ => mul_nonneg (crr_wordMass_nonneg hp x) ((c.enc_law x).1 m)
  have hq1 : ∑ m, q m = 1 := by
    show ∑ m, c.messageLaw p m = 1
    simp only [DistributionCompressionCode.messageLaw]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    simp [fun x => (c.enc_law x).2, crr_wordMass_sum hp]
  set N : ℕ := M * L with hN
  set k : Fin M → ℕ := fun m => ⌊(N : ℝ) * q m⌋₊ + 1 with hk
  set S : ℕ := ∑ m, k m with hS
  have hkl : ∀ m, (N : ℝ) * q m < k m := fun m => by
    simp only [hk]; push_cast; exact Nat.lt_floor_add_one _
  have hku : ∀ m, (k m : ℝ) ≤ N * q m + 1 := fun m => by
    simp only [hk]; push_cast
    have := Nat.floor_le (mul_nonneg (Nat.cast_nonneg N) (hq0 m))
    linarith
  haveI : Nonempty (Fin M) := ⟨⟨0, hMpos⟩⟩
  have hSreal : (S : ℝ) = ∑ m, (k m : ℝ) := by simp [hS]
  have hNS : (N : ℝ) < S := by
    rw [hSreal]
    calc (N : ℝ) = ∑ m, (N : ℝ) * q m := by rw [← Finset.mul_sum, hq1, mul_one]
      _ < ∑ m, (k m : ℝ) := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun m _ => hkl m
  have hSM : (S : ℝ) ≤ N + M := by
    rw [hSreal]
    calc ∑ m, (k m : ℝ) ≤ ∑ m, ((N : ℝ) * q m + 1) := Finset.sum_le_sum fun m _ => hku m
      _ = N + M := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, hq1]; simp
  have hSpos : 0 < S := by
    have : (0 : ℝ) < S := lt_of_le_of_lt (Nat.cast_nonneg N) hNS
    exact_mod_cast this
  have hSposR : (0 : ℝ) < S := by exact_mod_cast hSpos
  -- message assignment
  let msg : Fin S → Fin M := fun s => (finSigmaFinEquiv.symm s).1
  have hsum : ∀ g : Fin M → ℝ, ∑ s : Fin S, g (msg s) = ∑ m, (k m : ℝ) * g m := by
    intro g
    have h1 : ∑ s : Fin S, g (msg s) = ∑ σ : (m : Fin M) × Fin (k m), g σ.1 := by
      rw [← Equiv.sum_comp finSigmaFinEquiv.symm (fun σ : (m : Fin M) × Fin (k m) => g σ.1)]
    rw [h1, Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro m _
    show ∑ _y : Fin (k m), g m = _
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- posterior kernel
  let post : Fin M → SourceWord A n → ℝ := fun m x =>
    if 0 < q m then wordMass p x * c.enc x m / q m else 1 / (Fintype.card (SourceWord A n) : ℝ)
  have hpost : ∀ m, IsLaw (post m) := by
    intro m
    by_cases hm : 0 < q m
    · constructor
      · intro x
        simp only [post, hm, if_true]
        exact div_nonneg (mul_nonneg (crr_wordMass_nonneg hp x) ((c.enc_law x).1 m)) hm.le
      · simp only [post, hm, if_true]
        rw [← Finset.sum_div]
        exact div_self hm.ne'
    · constructor
      · intro x
        simp only [post, hm, if_false]
        positivity
      · simp only [post, hm, if_false]
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have : (0 : ℝ) < Fintype.card (SourceWord A n) := by exact_mod_cast Fintype.card_pos
        field_simp
  have hpostq : ∀ m x, q m * post m x = wordMass p x * c.enc x m := by
    intro m x
    by_cases hm : 0 < q m
    · simp only [post, hm, if_true]
      field_simp
    · have hm0 : q m = 0 := le_antisymm (not_lt.1 hm) (hq0 m)
      simp only [post, hm0, zero_mul]
      have : ∑ x, wordMass p x * c.enc x m = 0 := hm0
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun x _ =>
        mul_nonneg (crr_wordMass_nonneg hp x) ((c.enc_law x).1 m))] at this
      exact (this x (Finset.mem_univ x)).symm
  -- the product kernels
  let f : Fin M → SourceWord A n × SourceWord B n → ℝ := fun m z => post m z.1 * c.dec m z.2
  have hf : ∀ m, IsLaw (f m) := by
    intro m
    constructor
    · intro z; exact mul_nonneg ((hpost m).1 _) ((c.dec_law m).1 _)
    · simp only [f]
      rw [Fintype.sum_prod_type, ← Finset.sum_mul_sum, (hpost m).2, (c.dec_law m).2, mul_one]
  refine ⟨S, hSpos, ?_, fun s => post (msg s), fun s => c.dec (msg s), fun s => hpost _,
    fun s => c.dec_law _, ?_⟩
  · calc (S : ℝ) ≤ N + M := hSM
      _ = M * (L + 1) := by simp [hN]; ring
  · -- total variation estimate
    have hgen : generatedPairs (fun s => post (msg s)) (fun s => c.dec (msg s)) =
        fun z => ∑ m, ((k m : ℝ) / S) * f m z := by
      funext z
      simp only [generatedPairs]
      rw [hsum (fun m => post m z.1 * c.dec m z.2), Finset.sum_div]
      apply Finset.sum_congr rfl
      intro m _
      simp only [f]; ring
    have hmix : jointWordLaw p w = fun z => ∑ m, q m * f m z + (jointWordLaw p w z -
        wordMass p z.1 * c.output z.1 z.2) := by
      funext z
      have : ∑ m, q m * f m z = wordMass p z.1 * c.output z.1 z.2 := by
        simp only [f, DistributionCompressionCode.output, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _
        rw [← mul_assoc, hpostq, mul_assoc]
      rw [this]; ring
    have h1 : tv (jointWordLaw p w) (fun z => ∑ m, q m * f m z) ≤ error / 2 := by
      refine le_trans (le_of_eq ?_) hc
      simp only [tv, sourceAverageBlockError]
      rw [Fintype.sum_prod_type, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro x _
      have hmx := crr_wordMass_nonneg hp x
      rw [← mul_div_assoc, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro y _
      have : ∑ m, q m * f m (x, y) = wordMass p x * c.output x y := by
        simp only [f, DistributionCompressionCode.output, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _
        rw [← mul_assoc, hpostq, mul_assoc]
      rw [this]
      simp only [jointWordLaw]
      rw [← mul_sub, abs_mul, abs_of_nonneg hmx]
    have h2 : tv (fun z => ∑ m, q m * f m z) (fun z => ∑ m, ((k m : ℝ) / S) * f m z) ≤
        error / 2 := by
      refine le_trans (crr_tv_mix q (fun m => (k m : ℝ) / S) f hf) ?_
      apply div_le_div_of_nonneg_right _ (by norm_num)
      have hbound : ∀ m, |q m - (k m : ℝ) / S| ≤ q m * M / S + 1 / S := by
        intro m
        have hkm_l := hkl m
        have hkm_u := hku m
        have hqm := hq0 m
        have hqS := mul_nonneg hqm (sub_nonneg.2 hNS.le)
        have hqM := mul_nonneg hqm (Nat.cast_nonneg M)
        have e2 : q m * M / S + 1 / S = (q m * M + 1) / S := by rw [add_div]
        rw [abs_sub_le_iff, e2]
        constructor
        · have e1 : q m - k m / S = (q m * S - k m) / S := by field_simp
          rw [e1]
          apply div_le_div_of_nonneg_right _ hSposR.le
          nlinarith
        · have e1 : k m / S - q m = (k m - q m * S) / S := by field_simp
          rw [e1]
          apply div_le_div_of_nonneg_right _ hSposR.le
          nlinarith
      calc ∑ m, |q m - (k m : ℝ) / S| ≤ ∑ m, (q m * M / S + 1 / S) :=
            Finset.sum_le_sum fun m _ => hbound m
        _ = 2 * M / S := by
            rw [Finset.sum_add_distrib]
            simp only [div_eq_mul_inv]
            rw [← Finset.sum_mul, ← Finset.sum_mul, hq1]
            simp; ring
        _ ≤ 2 * M / N := by
            have hNpos : (0 : ℝ) < N := by
              rw [hN]; push_cast; exact mul_pos (by exact_mod_cast hMpos) hLpos
            apply div_le_div_of_nonneg_left (by positivity) hNpos hNS.le
        _ = 2 / L := by
            rw [hN]; push_cast
            have : (M : ℝ) ≠ 0 := by exact_mod_cast hMpos.ne'
            field_simp
        _ ≤ error := by
            rw [div_le_iff₀ hLpos]
            rw [div_le_iff₀ he] at hL
            linarith
    calc tv (jointWordLaw p w) (generatedPairs (fun s => post (msg s)) (fun s => c.dec (msg s)))
        ≤ tv (jointWordLaw p w) (fun z => ∑ m, q m * f m z) +
          tv (fun z => ∑ m, q m * f m z)
            (generatedPairs (fun s => post (msg s)) (fun s => c.dec (msg s))) :=
          crr_tv_triangle _ _ _
      _ ≤ error / 2 + error / 2 := by
          rw [hgen]; exact add_le_add h1 h2
      _ = error := by ring

/-! ### Main theorem -/

theorem solution (hquestion : QuestionFour)
    {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (p : A → ℝ) (w : A → B → ℝ) (hp : IsLaw p) (hw : IsStochastic w)
    (error slack : ℝ) (he : 0 < error) (hs : 0 < slack) :
    ∃ threshold : ℕ, ∀ n ≥ threshold, 0 < n →
      ∃ seeds : ℕ, 0 < seeds ∧ Real.logb 2 (seeds : ℝ) / n ≤ sourceInformationBits p w + slack ∧
        ∃ (a : Fin seeds → SourceWord A n → ℝ) (b : Fin seeds → SourceWord B n → ℝ),
          IsStochastic a ∧ IsStochastic b ∧
          tv (jointWordLaw p w) (generatedPairs a b) ≤ error := by
  classical
  -- the code error level: half of `error`, but below 1
  set ε : ℝ := min (error / 2) (1 / 2) with hε
  have hε0 : 0 < ε := lt_min (by positivity) (by norm_num)
  have hε1 : ε < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hεe : ε ≤ error / 2 := min_le_left _ _
  -- the seed multiplicity
  set L : ℕ := ⌈2 / error⌉₊ with hL
  have hLge : 2 / error ≤ L := Nat.le_ceil _
  have hL1 : (0 : ℝ) < (L : ℝ) + 1 := by positivity
  obtain ⟨N, hN⟩ := crr_sizeRate_bound hquestion p w hp hw ε hε0 hε1 (slack / 2) (by positivity)
  -- threshold handling the additive constant
  set C : ℝ := Real.logb 2 ((L : ℝ) + 1) with hC
  have hC0 : 0 ≤ C := Real.logb_nonneg (by norm_num) (by linarith [(Nat.cast_nonneg L : (0:ℝ) ≤ L)])
  obtain ⟨N2, hN2⟩ : ∃ N2 : ℕ, 2 * C / slack ≤ N2 := ⟨⌈2 * C / slack⌉₊, Nat.le_ceil _⟩
  refine ⟨N + N2 + 1, fun n hn hn0 => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hmN : N ≤ m := by omega
  have hmN2 : N2 ≤ m := by omega
  obtain ⟨c, hcsize, hcerr⟩ := crr_minimumSize_mem p w hw (m + 1) ε hε0.le
  have hcerr' : sourceAverageBlockError p w c.output ≤ error / 2 := hcerr.trans hεe
  obtain ⟨seeds, hseeds, hseedsle, a, b, ha, hb, htv⟩ :=
    crr_construct p w hp c error he hcerr' L hLge
  refine ⟨seeds, hseeds, ?_, a, b, ha, hb, htv⟩
  -- the rate bound
  have hnpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hsize : Real.logb 2 (c.size : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * (sourceInformationBits p w + slack / 2) := by
    rw [hcsize]; push_cast; exact hN m hmN
  have hcpos : (0 : ℝ) < c.size := by exact_mod_cast c.size_pos
  have hlog : Real.logb 2 (seeds : ℝ) ≤ Real.logb 2 (c.size : ℝ) + C := by
    rw [hC, ← Real.logb_mul hcpos.ne' hL1.ne']
    apply Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hseeds) hseedsle
  rw [div_le_iff₀ hnpos]
  have hCm : C ≤ ((m + 1 : ℕ) : ℝ) * (slack / 2) := by
    have h1 : 2 * C / slack ≤ ((m + 1 : ℕ) : ℝ) := by
      refine hN2.trans ?_
      exact_mod_cast (by omega : N2 ≤ m + 1)
    rw [div_le_iff₀ hs] at h1
    linarith
  calc Real.logb 2 (seeds : ℝ) ≤ Real.logb 2 (c.size : ℝ) + C := hlog
    _ ≤ ((m + 1 : ℕ) : ℝ) * (sourceInformationBits p w + slack / 2) +
        ((m + 1 : ℕ) : ℝ) * (slack / 2) := add_le_add hsize hCm
    _ = (sourceInformationBits p w + slack) * ((m + 1 : ℕ) : ℝ) := by ring
