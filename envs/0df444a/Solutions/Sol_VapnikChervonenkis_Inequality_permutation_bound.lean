-- Prove2me | solution 1 for VapnikChervonenkis.Inequality.permutation_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T06:41:08.745385+00:00
-- url     : https://prove2.me/submissions/64182871-7a36-4788-ae1e-02e052bdc7d8

import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_index
import Definitions.Def_VapnikChervonenkis_Shared_growthFunction
import Definitions.Def_VapnikChervonenkis_Shared_deviation

set_option autoImplicit false

open Finset in
lemma cde_hoeff_count {l : ℕ} (hl : 1 ≤ l) (c : Fin l → ℝ) (hc : ∀ i, |c i| ≤ 1) {t : ℝ}
    (ht : 0 ≤ t) :
    ((Finset.univ.filter fun s : Fin l → Bool =>
        t ≤ ∑ i, (if s i then (1 : ℝ) else -1) * c i).card : ℝ)
      ≤ (2 : ℝ) ^ l * Real.exp (-(t ^ 2 / (2 * l))) := by
  classical
  have hlpos : (0 : ℝ) < l := by exact_mod_cast hl
  set lam : ℝ := t / l with hlam
  have hlam0 : 0 ≤ lam := div_nonneg ht hlpos.le
  have hmark : ((Finset.univ.filter fun s : Fin l → Bool =>
        t ≤ ∑ i, (if s i then (1 : ℝ) else -1) * c i).card : ℝ) * Real.exp (lam * t)
      ≤ ∑ s : Fin l → Bool, Real.exp (lam * ∑ i, (if s i then (1 : ℝ) else -1) * c i) := by
    rw [Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun s _ => ?_
    by_cases h : t ≤ ∑ i, (if s i then (1 : ℝ) else -1) * c i
    · simp only [h, if_true, Nat.cast_one, one_mul]
      exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h hlam0)
    · simp only [h, if_false, Nat.cast_zero, zero_mul]
      exact (Real.exp_pos _).le
  have hprod : ∑ s : Fin l → Bool, Real.exp (lam * ∑ i, (if s i then (1 : ℝ) else -1) * c i)
      = ∏ i : Fin l, (Real.exp (lam * c i) + Real.exp (-(lam * c i))) := by
    have h1 : ∀ s : Fin l → Bool, Real.exp (lam * ∑ i, (if s i then (1 : ℝ) else -1) * c i)
        = ∏ i : Fin l, Real.exp (lam * ((if s i then (1 : ℝ) else -1) * c i)) := by
      intro s
      rw [Finset.mul_sum, Real.exp_sum]
    simp_rw [h1]
    have := Finset.prod_univ_sum (fun _ : Fin l => (Finset.univ : Finset Bool))
      (fun i b => Real.exp (lam * ((if b then (1 : ℝ) else -1) * c i)))
    rw [Fintype.piFinset_univ] at this
    rw [← this]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Fintype.sum_bool]
    simp only [if_true, Bool.false_eq_true, if_false, one_mul, neg_one_mul, mul_neg]
  have hfac : ∀ i : Fin l, Real.exp (lam * c i) + Real.exp (-(lam * c i))
      ≤ 2 * Real.exp (lam ^ 2 / 2) := by
    intro i
    have h1 := Real.cosh_le_exp_half_sq (lam * c i)
    rw [Real.cosh_eq] at h1
    have h2 : (lam * c i) ^ 2 ≤ lam ^ 2 := by
      have : |lam * c i| ≤ lam := by
        rw [abs_mul, abs_of_nonneg hlam0]
        calc lam * |c i| ≤ lam * 1 := mul_le_mul_of_nonneg_left (hc i) hlam0
          _ = lam := mul_one _
      have h3 := sq_le_sq' (by linarith [abs_nonneg (lam * c i), neg_abs_le (lam * c i)] : -lam ≤ lam * c i)
        (le_trans (le_abs_self _) this)
      exact h3
    have h4 : Real.exp ((lam * c i) ^ 2 / 2) ≤ Real.exp (lam ^ 2 / 2) :=
      Real.exp_le_exp.2 (by linarith)
    linarith
  have hprod2 : ∏ i : Fin l, (Real.exp (lam * c i) + Real.exp (-(lam * c i)))
      ≤ (2 * Real.exp (lam ^ 2 / 2)) ^ l := by
    calc _ ≤ ∏ _i : Fin l, (2 * Real.exp (lam ^ 2 / 2)) :=
          Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => hfac i)
      _ = _ := by simp
  have hexp : Real.exp (lam * t) * Real.exp (-(t ^ 2 / (2 * l))) = Real.exp (lam ^ 2 / 2 * l) := by
    rw [← Real.exp_add]
    congr 1
    rw [hlam]
    field_simp
    ring
  have hpow : (2 * Real.exp (lam ^ 2 / 2)) ^ l = 2 ^ l * Real.exp (lam ^ 2 / 2 * l) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    ring
  have hcount : ((Finset.univ.filter fun s : Fin l → Bool =>
        t ≤ ∑ i, (if s i then (1 : ℝ) else -1) * c i).card : ℝ) * Real.exp (lam * t)
      ≤ 2 ^ l * Real.exp (lam ^ 2 / 2 * l) := by
    rw [← hpow]; rw [hprod] at hmark; exact hmark.trans hprod2
  rw [← hexp] at hcount
  have hpos : 0 < Real.exp (lam * t) := Real.exp_pos _
  have := hcount
  rw [show (2 : ℝ) ^ l * (Real.exp (lam * t) * Real.exp (-(t ^ 2 / (2 * l))))
      = (2 ^ l * Real.exp (-(t ^ 2 / (2 * l)))) * Real.exp (lam * t) by ring] at this
  exact le_of_mul_le_mul_right this hpos


/-- Swap the two halves at the positions where `τ` is `true`. -/
def cdeSwS (l : ℕ) (τ : Fin l → Bool) : Fin l ⊕ Fin l → Fin l ⊕ Fin l
  | Sum.inl i => if τ i then Sum.inr i else Sum.inl i
  | Sum.inr i => if τ i then Sum.inl i else Sum.inr i

lemma cdeSwS_inv (l : ℕ) (τ : Fin l → Bool) : Function.Involutive (cdeSwS l τ) := by
  intro a
  cases a with
  | inl i => by_cases h : τ i <;> simp [cdeSwS, h]
  | inr i => by_cases h : τ i <;> simp [cdeSwS, h]

def cdeSw (l : ℕ) (τ : Fin l → Bool) : Equiv.Perm (Fin (l + l)) :=
  (finSumFinEquiv.symm.trans (Function.Involutive.toPerm _ (cdeSwS_inv l τ))).trans finSumFinEquiv

lemma cdeSw_castAdd (l : ℕ) (τ : Fin l → Bool) (i : Fin l) :
    cdeSw l τ (Fin.castAdd l i) = if τ i then Fin.natAdd l i else Fin.castAdd l i := by
  by_cases h : τ i <;> simp [cdeSw, cdeSwS, h]

lemma cdeSw_natAdd (l : ℕ) (τ : Fin l → Bool) (i : Fin l) :
    cdeSw l τ (Fin.natAdd l i) = if τ i then Fin.castAdd l i else Fin.natAdd l i := by
  simp only [cdeSw, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd,
    Function.Involutive.coe_toPerm, cdeSwS]
  by_cases h : τ i <;> simp only [h, if_true, Bool.false_eq_true, if_false, ↓reduceIte,
    finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]

open VapnikChervonenkis.Shared in
lemma cde_sup_attained {X : Type*} (S : Set (Set X)) (l : ℕ) (z : Fin (l + l) → X) {r : ℝ}
    (hr : 0 < r) (h : r ≤ semiSampleDeviation S l z) :
    ∃ A ∈ S, r ≤ |relFreq A (fun i : Fin l => z (Fin.castAdd l i))
      - relFreq A (fun i : Fin l => z (Fin.natAdd l i))| := by
  classical
  unfold semiSampleDeviation at h
  set f : S → ℝ := fun A => |relFreq (A : Set X) (fun i : Fin l => z (Fin.castAdd l i))
      - relFreq (A : Set X) (fun i : Fin l => z (Fin.natAdd l i))| with hf
  by_cases hne : Nonempty S
  · set F : Finset (Fin (l + l)) → ℝ := fun t =>
      |((Finset.univ.filter (fun i : Fin l => Fin.castAdd l i ∈ t)).card : ℝ) / l
        - ((Finset.univ.filter (fun i : Fin l => Fin.natAdd l i ∈ t)).card : ℝ) / l| with hF
    have hfF : ∀ A : S, f A = F (Finset.univ.filter (fun j => z j ∈ (A : Set X))) := by
      intro A
      simp only [hf, hF, relFreq, Finset.mem_filter, Finset.mem_univ, true_and]
    have hfin : (Set.range f).Finite := by
      refine (Set.finite_range F).subset ?_
      rintro _ ⟨A, rfl⟩
      exact ⟨_, (hfF A).symm⟩
    have hmem := Set.Nonempty.csSup_mem (Set.range_nonempty f) hfin
    obtain ⟨A, hA⟩ := hmem
    refine ⟨A, A.2, ?_⟩
    have : r ≤ f A := by rw [hA]; exact h
    exact this
  · rw [not_nonempty_iff] at hne
    rw [Real.iSup_of_isEmpty] at h
    linarith

open VapnikChervonenkis.Shared in
lemma cde_count {X : Type*} (S : Set (Set X)) (l : ℕ) (hl1 : 1 ≤ l) {ε : ℝ} (hε : 0 < ε)
    (y : Fin (l + l) → X) :
    ((Finset.univ.filter fun τ : Fin l → Bool =>
        ε / 2 ≤ semiSampleDeviation S l (y ∘ cdeSw l τ)).card : ℝ)
      ≤ (index S y : ℝ) * (2 * ((2 : ℝ) ^ l * Real.exp (-(ε ^ 2 * l / 8)))) := by
  classical
  have hlpos : (0 : ℝ) < l := by exact_mod_cast hl1
  set T : Finset (Finset (Fin (l + l))) :=
    Finset.univ.filter (fun t : Finset (Fin (l + l)) => ∃ A ∈ S, ∀ i, i ∈ t ↔ y i ∈ A) with hT
  have hTcard : T.card = index S y := by
    unfold index
    first | rfl | congr
  set c : Finset (Fin (l + l)) → Fin l → ℝ := fun t i =>
    (if Fin.castAdd l i ∈ t then (1 : ℝ) else 0) - (if Fin.natAdd l i ∈ t then (1 : ℝ) else 0)
    with hc
  have hc1 : ∀ t i, |c t i| ≤ 1 := by
    intro t i
    simp only [hc]
    rw [abs_le]
    by_cases h1 : Fin.castAdd l i ∈ t <;> by_cases h2 : Fin.natAdd l i ∈ t <;>
      simp only [h1, h2, if_true, if_false, ↓reduceIte] <;> norm_num
  set Bad : Finset (Fin (l + l)) → Finset (Fin l → Bool) := fun t =>
    Finset.univ.filter (fun σ : Fin l → Bool =>
      (l : ℝ) * (ε / 2) ≤ |∑ i, (if σ i then (1 : ℝ) else -1) * c t i|) with hBad
  have hBadcard : ∀ t, ((Bad t).card : ℝ) ≤ 2 * ((2 : ℝ) ^ l * Real.exp (-(ε ^ 2 * l / 8))) := by
    intro t
    have hexp : (l * (ε / 2)) ^ 2 / (2 * (l : ℝ)) = ε ^ 2 * l / 8 := by
      field_simp; ring
    have hnn : 0 ≤ (l : ℝ) * (ε / 2) := by positivity
    have h1 := cde_hoeff_count hl1 (c t) (hc1 t) hnn
    have h2 := cde_hoeff_count hl1 (fun i => - c t i)
      (fun i => by simpa [abs_neg] using hc1 t i) hnn
    beta_reduce at h2
    rw [hexp] at h1 h2
    have hsub : Bad t ⊆
        (Finset.univ.filter fun s : Fin l → Bool =>
          (l : ℝ) * (ε / 2) ≤ ∑ i, (if s i then (1 : ℝ) else -1) * c t i) ∪
        (Finset.univ.filter fun s : Fin l → Bool =>
          (l : ℝ) * (ε / 2) ≤ ∑ i, (if s i then (1 : ℝ) else -1) * (- c t i)) := by
      intro σ hσ
      simp only [hBad, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hσ ⊢
      have hneg : ∑ i, (if σ i then (1 : ℝ) else -1) * (- c t i)
          = - ∑ i, (if σ i then (1 : ℝ) else -1) * c t i := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [hneg]
      rcases le_abs'.1 hσ with h | h
      · right; linarith
      · left; linarith
    have := (Nat.cast_le (α := ℝ)).2 ((Finset.card_le_card hsub).trans (Finset.card_union_le _ _))
    push_cast at this
    linarith
  have hsubset : (Finset.univ.filter fun τ : Fin l → Bool =>
        ε / 2 ≤ semiSampleDeviation S l (y ∘ cdeSw l τ)) ⊆ T.biUnion Bad := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    obtain ⟨A, hAS, hA⟩ := cde_sup_attained S l (y ∘ cdeSw l σ) (by positivity) hσ
    refine Finset.mem_biUnion.2 ⟨Finset.univ.filter (fun j : Fin (l + l) => y j ∈ A), ?_, ?_⟩
    · simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨A, hAS, fun i => by simp⟩
    · simp only [hBad, Finset.mem_filter, Finset.mem_univ, true_and]
      set tA : Finset (Fin (l + l)) := Finset.univ.filter (fun j : Fin (l + l) => y j ∈ A)
        with htA
      have hci : ∀ i : Fin l, c tA i
          = (if y (Fin.castAdd l i) ∈ A then (1 : ℝ) else 0)
            - (if y (Fin.natAdd l i) ∈ A then (1 : ℝ) else 0) := by
        intro i
        simp only [hc, htA, Finset.mem_filter, Finset.mem_univ, true_and]
      have hdiff : relFreq A (fun i : Fin l => (y ∘ cdeSw l σ) (Fin.castAdd l i))
          - relFreq A (fun i : Fin l => (y ∘ cdeSw l σ) (Fin.natAdd l i))
          = - (∑ i, (if σ i then (1 : ℝ) else -1) * c tA i) / l := by
        unfold relFreq
        rw [Finset.card_filter, Finset.card_filter, Nat.cast_sum, Nat.cast_sum, ← sub_div,
          ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hci i]
        simp only [Function.comp_apply, cdeSw_castAdd, cdeSw_natAdd]
        by_cases h : σ i <;> by_cases h1 : y (Fin.castAdd l i) ∈ A <;>
          by_cases h2 : y (Fin.natAdd l i) ∈ A <;>
          simp only [h, h1, h2, if_true, if_false, Bool.false_eq_true, ↓reduceIte] <;> norm_num
      rw [hdiff, abs_div, abs_neg, abs_of_pos hlpos, le_div_iff₀ hlpos] at hA
      linarith
  have hcard1 := Finset.card_le_card hsubset
  have hcard2 := hcard1.trans Finset.card_biUnion_le
  have hcard3 : ((Finset.univ.filter fun τ : Fin l → Bool =>
        ε / 2 ≤ semiSampleDeviation S l (y ∘ cdeSw l τ)).card : ℝ)
      ≤ ∑ t ∈ T, ((Bad t).card : ℝ) := by
    exact_mod_cast hcard2
  calc _ ≤ ∑ t ∈ T, ((Bad t).card : ℝ) := hcard3
    _ ≤ ∑ _t ∈ T, 2 * ((2 : ℝ) ^ l * Real.exp (-(ε ^ 2 * l / 8))) :=
        Finset.sum_le_sum fun t _ => hBadcard t
    _ = (T.card : ℝ) * (2 * ((2 : ℝ) ^ l * Real.exp (-(ε ^ 2 * l / 8)))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = _ := by rw [hTcard]

open VapnikChervonenkis.Shared in
lemma cde_index_perm {X : Type*} (S : Set (Set X)) {r : ℕ} (x : Fin r → X)
    (σ : Equiv.Perm (Fin r)) : index S (x ∘ σ) = index S x := by
  classical
  unfold index
  refine Finset.card_equiv (Equiv.finsetCongr σ) ?_
  intro t
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]
  constructor
  · rintro ⟨A, hA, ht⟩
    refine ⟨A, hA, fun j => ?_⟩
    rw [Equiv.finsetCongr_apply, Finset.mem_map_equiv, ht]
    simp
  · rintro ⟨A, hA, ht⟩
    refine ⟨A, hA, fun i => ?_⟩
    have := ht (σ i)
    rw [Equiv.finsetCongr_apply, Finset.mem_map_equiv] at this
    simpa using this

open VapnikChervonenkis in
theorem solution {X : Type*} (S : Set (Set X)) (ε : ℝ) (l : ℕ) (hl : 1 ≤ l)
    (hε : 0 < ε) (x : Fin (l + l) → X) :
    ((Finset.univ.filter (fun σ : Equiv.Perm (Fin (l + l)) =>
        ε / 2 ≤ Shared.semiSampleDeviation S l (x ∘ σ))).card : ℝ) / ((l + l).factorial : ℝ)
      ≤ 2 * (Shared.index S x : ℝ) * Real.exp (-(ε ^ 2 * l / 8)) := by
  classical
  set K : ℝ := 2 * ((2 : ℝ) ^ l * Real.exp (-(ε ^ 2 * l / 8))) with hK
  set Bad : Equiv.Perm (Fin (l + l)) → Prop :=
    fun σ => ε / 2 ≤ Shared.semiSampleDeviation S l (x ∘ σ) with hBad
  set P := Finset.univ.filter (fun σ : Equiv.Perm (Fin (l + l)) => Bad σ) with hP
  have hshift : ∀ τ : Fin l → Bool,
      (Finset.univ.filter (fun σ : Equiv.Perm (Fin (l + l)) => Bad (σ * cdeSw l τ))).card
        = P.card := by
    intro τ
    refine Finset.card_equiv (Equiv.mulRight (cdeSw l τ)) ?_
    intro σ
    simp [hP]
  have hcomp : ∀ (σ : Equiv.Perm (Fin (l + l))) (τ : Fin l → Bool),
      x ∘ ⇑(σ * cdeSw l τ) = (x ∘ ⇑σ) ∘ ⇑(cdeSw l τ) := by
    intro σ τ
    rw [Equiv.Perm.coe_mul]
    rfl
  have hsum : (2 : ℝ) ^ l * (P.card : ℝ)
      = ∑ σ : Equiv.Perm (Fin (l + l)),
          ((Finset.univ.filter fun τ : Fin l → Bool =>
            ε / 2 ≤ Shared.semiSampleDeviation S l ((x ∘ ⇑σ) ∘ cdeSw l τ)).card : ℝ) := by
    have h1 : (2 : ℝ) ^ l * (P.card : ℝ) = ∑ τ : Fin l → Bool,
        ((Finset.univ.filter (fun σ : Equiv.Perm (Fin (l + l)) => Bad (σ * cdeSw l τ))).card : ℝ) := by
      simp only [hshift, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
    rw [h1]
    simp only [Finset.card_filter, Nat.cast_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
    simp only [hBad, hcomp]
  have hbound : (2 : ℝ) ^ l * (P.card : ℝ)
      ≤ ((l + l).factorial : ℝ) * ((Shared.index S x : ℝ) * K) := by
    rw [hsum]
    calc _ ≤ ∑ _σ : Equiv.Perm (Fin (l + l)), (Shared.index S x : ℝ) * K := by
          refine Finset.sum_le_sum fun σ _ => ?_
          have := cde_count S l hl hε (x ∘ ⇑σ)
          rw [cde_index_perm] at this
          exact this
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
            nsmul_eq_mul]
  have hfac : (0 : ℝ) < ((l + l).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have h2l : (0 : ℝ) < (2 : ℝ) ^ l := by positivity
  rw [div_le_iff₀ hfac]
  have : (P.card : ℝ) ≤ ((l + l).factorial : ℝ) * (Shared.index S x : ℝ)
      * (2 * Real.exp (-(ε ^ 2 * l / 8))) := by
    have h3 : (2 : ℝ) ^ l * (P.card : ℝ) ≤ (2 : ℝ) ^ l * (((l + l).factorial : ℝ)
        * (Shared.index S x : ℝ) * (2 * Real.exp (-(ε ^ 2 * l / 8)))) := by
      calc _ ≤ _ := hbound
        _ = _ := by rw [hK]; ring
    exact le_of_mul_le_mul_left h3 h2l
  calc _ ≤ _ := this
    _ = _ := by ring
