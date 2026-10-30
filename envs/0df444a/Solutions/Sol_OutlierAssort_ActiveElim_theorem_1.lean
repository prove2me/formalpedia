-- Prove2me | solution 1 for OutlierAssort.ActiveElim.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T17:17:54.984992+00:00
-- url     : https://prove2.me/submissions/e47b7cea-ae94-47d7-a529-82c8ebfc4049
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_OutlierAssort_ActiveElim_Model
import Definitions.Def_OutlierAssort_ActiveElim_Algorithm
import Theorems.Thm_OutlierAssort_ActiveElim_lemma_3
import Theorems.Thm_OutlierAssort_ActiveElim_lemma_4
import Theorems.Thm_OutlierAssort_ActiveElim_regret_sum_bound

open OutlierAssort.ActiveElim

namespace OARed

theorem restrict_snoc {α : Type*} {n : ℕ} (h : Fin n → α) (x : α) (s : ℕ) (hs : s ≤ n) :
    restrict (Fin.snoc (α := fun _ => α) h x) s (hs.trans (Nat.le_succ n)) = restrict h s hs := by
  funext u
  simp only [restrict]
  have : (Fin.castLE (hs.trans (Nat.le_succ n)) u : Fin (n + 1)) = Fin.castSucc (Fin.castLE hs u) := by
    ext; simp
  rw [this, Fin.snoc_castSucc]

theorem tree_sum {α : Type*} [Fintype α] (f : (t : ℕ) → (Fin t → α) → α → ℝ)
    (hf0 : ∀ t p x, 0 ≤ f t p x) (hf1 : ∀ t p, ∑ x, f t p x ≤ 1) :
    ∀ n : ℕ, ∑ h : Fin n → α, ∏ t : Fin n, f t.val (restrict h t.val t.isLt.le) (h t) ≤ 1 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← (Fin.snocEquiv (fun _ => α)).sum_comp, Fintype.sum_prod_type]
    have key : ∀ (x : α) (h : Fin n → α),
        ∏ t : Fin (n + 1), f t.val (restrict ((Fin.snocEquiv (fun _ => α)) (x, h)) t.val t.isLt.le)
            (((Fin.snocEquiv (fun _ => α)) (x, h)) t) =
          (∏ t : Fin n, f t.val (restrict h t.val t.isLt.le) (h t)) * f n h x := by
      intro x h
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.snocEquiv_apply, Fin.val_castSucc, Fin.val_last, Fin.snoc_castSucc, Fin.snoc_last]
      have hr : ∀ (s : ℕ) (hs : s ≤ n),
          restrict ((Fin.snocEquiv (fun _ => α)) (x, h)) s (hs.trans (Nat.le_succ n)) = restrict h s hs := by
        intro s hs
        funext u
        simp only [restrict, Fin.snocEquiv_apply]
        have : (Fin.castLE (hs.trans (Nat.le_succ n)) u : Fin (n + 1)) = Fin.castSucc (Fin.castLE hs u) := by
          ext; simp
        rw [this, Fin.snoc_castSucc]
      congr 1
      · refine Finset.prod_congr rfl (fun t _ => ?_)
        rw [hr t.val t.isLt.le]
      · congr 1
        rw [hr n le_rfl]
        funext u
        simp [restrict]
    simp_rw [key]
    rw [Finset.sum_comm]
    calc ∑ y : Fin n → α, ∑ x : α, (∏ t : Fin n, f t.val (restrict y t.val t.isLt.le) (y t)) * f n y x
        = ∑ y : Fin n → α, (∏ t : Fin n, f t.val (restrict y t.val t.isLt.le) (y t)) * ∑ x, f n y x := by
          simp_rw [Finset.mul_sum]
      _ ≤ ∑ y : Fin n → α, (∏ t : Fin n, f t.val (restrict y t.val t.isLt.le) (y t)) * 1 := by
          apply Finset.sum_le_sum; intro y _
          exact mul_le_mul_of_nonneg_left (hf1 _ _)
            (Finset.prod_nonneg (fun t _ => hf0 _ _ _))
      _ ≤ 1 := by simpa using ih

/-! ### Locality of the state -/

theorem purchCount_restrict {N T m : ℕ} (h : Fin T → Rec N) (hm : m ≤ T) (a b : ℕ) (hb : b ≤ m)
    (i : Fin N) : purchCount (restrict h m hm) a b i = purchCount h a b i := by
  unfold purchCount
  refine Finset.card_bij (fun s _ => Fin.castLE hm s) ?_ ?_ ?_
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    simpa [restrict] using hs
  · intro s _ s' _ hss
    exact Fin.castLE_injective hm hss
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    refine ⟨⟨s.val, lt_of_lt_of_le hs.2.1 hb⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [restrict] using hs
    · ext; simp

theorem noPurchCount_restrict {N T m : ℕ} (h : Fin T → Rec N) (hm : m ≤ T) (a b : ℕ) (hb : b ≤ m)
    (i : Fin N) : noPurchCount (restrict h m hm) a b i = noPurchCount h a b i := by
  unfold noPurchCount
  refine Finset.card_bij (fun s _ => Fin.castLE hm s) ?_ ?_ ?_
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    simpa [restrict] using hs
  · intro s _ s' _ hss
    exact Fin.castLE_injective hm hss
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    refine ⟨⟨s.val, lt_of_lt_of_le hs.2.1 hb⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [restrict] using hs
    · ext; simp

theorem epochStart_succ (N K T τ : ℕ) :
    epochStart N K T (τ + 1) = epochStart N K T τ + epochLen N K T τ := by
  simp [epochStart, Finset.sum_range_succ]

theorem epochStart_mono (N K T : ℕ) {τ τ' : ℕ} (h : τ ≤ τ') :
    epochStart N K T τ ≤ epochStart N K T τ' := by
  unfold epochStart
  exact Finset.sum_le_sum_of_subset (Finset.range_mono h)

theorem state_restrict {N : ℕ} (alg : Input N) (h : Fin alg.T → Rec N) {m : ℕ} (hm : m ≤ alg.T) :
    ∀ τ, epochStart N alg.K alg.T τ ≤ m → state alg (restrict h m hm) τ = state alg h τ := by
  intro τ
  induction τ with
  | zero => intro _; rfl
  | succ τ ih =>
    intro hτ
    have h1 : epochStart N alg.K alg.T τ ≤ m := (epochStart_mono _ _ _ (Nat.le_succ τ)).trans hτ
    have h2 : epochStart N alg.K alg.T τ + epochLen N alg.K alg.T τ ≤ m := by
      rw [← epochStart_succ]; exact hτ
    simp only [state]
    rw [ih h1]
    congr 1
    funext i
    rw [purchCount_restrict h hm _ _ h2, noPurchCount_restrict h hm _ _ h2]

/-! ### Epoch bookkeeping -/

theorem epochLen_pos {N K T : ℕ} (h0 : 1 ≤ T0 N K T) (τ : ℕ) : 1 ≤ epochLen N K T τ := by
  unfold epochLen
  exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by positivity) (by omega))

theorem le_epochStart {N K T : ℕ} (h0 : 1 ≤ T0 N K T) (τ : ℕ) : τ ≤ epochStart N K T τ := by
  induction τ with
  | zero => simp
  | succ τ ih => rw [epochStart_succ]; have := epochLen_pos h0 τ; omega

theorem epochOf_spec {N K T : ℕ} (t : ℕ) :
    epochStart N K T (epochOf N K T t) ≤ t ∧ epochOf N K T t ≤ t := by
  classical
  unfold epochOf
  have hne : ((Finset.range (t + 1)).filter (fun τ => epochStart N K T τ ≤ t)).Nonempty :=
    ⟨0, Finset.mem_filter.2 ⟨by simp, by simp [epochStart]⟩⟩
  obtain ⟨τ, hτ, heq⟩ := Finset.exists_mem_eq_sup _ hne id
  convert (show epochStart N K T τ ≤ t ∧ τ ≤ t from ?_) using 2 <;> try simp only [heq, id]
  simp only [Finset.mem_filter, Finset.mem_range] at hτ
  exact ⟨hτ.2, by omega⟩

theorem lt_epochStart_epochOf_succ {N K T : ℕ} (h0 : 1 ≤ T0 N K T) (t : ℕ) :
    t < epochStart N K T (epochOf N K T t + 1) := by
  classical
  by_contra hc
  push Not at hc
  have hle := le_epochStart h0 (epochOf N K T t + 1)
  have hmem : epochOf N K T t + 1 ∈ (Finset.range (t + 1)).filter (fun τ => epochStart N K T τ ≤ t) := by
    simp only [Finset.mem_filter, Finset.mem_range]; omega
  have : epochOf N K T t + 1 ≤ epochOf N K T t := Finset.le_sup (f := id) hmem
  omega

theorem epochOf_mono {N K T : ℕ} {t t' : ℕ} (h : t ≤ t') : epochOf N K T t ≤ epochOf N K T t' := by
  classical
  unfold epochOf
  apply Finset.sup_le
  intro τ hτ
  simp only [Finset.mem_filter, Finset.mem_range] at hτ
  have hmem : τ ∈ (Finset.range (t' + 1)).filter (fun τ => epochStart N K T τ ≤ t') := by
    simp only [Finset.mem_filter, Finset.mem_range]; omega
  exact Finset.le_sup (f := id) hmem

theorem sum_epochs_le {N K T : ℕ} (h0 : 1 ≤ T0 N K T) (c : ℕ → ℝ) (hc : ∀ τ, 0 ≤ c τ) :
    ∑ t : Fin T, c (epochOf N K T t.val) ≤
      ∑ τ ∈ Finset.range (tau0 N K T + 1), c τ * (epochLen N K T τ : ℝ) := by
  classical
  have hmaps : ∀ t ∈ (Finset.univ : Finset (Fin T)),
      epochOf N K T t.val ∈ Finset.range (tau0 N K T + 1) := by
    intro t _
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact epochOf_mono (by omega)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_le_sum
  intro τ _
  rw [Finset.sum_congr rfl (fun t ht => by rw [(Finset.mem_filter.1 ht).2]), Finset.sum_const,
    nsmul_eq_mul, mul_comm]
  apply mul_le_mul_of_nonneg_left _ (hc τ)
  norm_cast
  calc (Finset.univ.filter (fun t : Fin T => epochOf N K T t.val = τ)).card
      ≤ (Finset.Ico (epochStart N K T τ) (epochStart N K T τ + epochLen N K T τ)).card := by
        apply Finset.card_le_card_of_injOn (fun t => t.val)
        · intro t ht
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht
          simp only [Finset.coe_Ico, Set.mem_Ico]
          have h1 := (epochOf_spec (N := N) (K := K) (T := T) t.val).1
          have h2 := lt_epochStart_epochOf_succ h0 t.val
          rw [ht] at h1 h2
          rw [epochStart_succ] at h2
          exact ⟨h1, h2⟩
        · intro a _ b _ hab; exact Fin.ext hab
    _ = epochLen N K T τ := by simp

/-! ### The path law -/

theorem mnlLaw_nonneg {N : ℕ} (v : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (S : Finset (Fin N))
    (o : Option (Fin N)) : 0 ≤ mnlLaw v S o := by
  have hV : 0 < 1 + ∑ j ∈ S, v j := by
    have := Finset.sum_nonneg (fun j (_ : j ∈ S) => hv j); linarith
  cases o with
  | none => simp only [mnlLaw]; positivity
  | some i =>
    simp only [mnlLaw]
    split_ifs
    · exact div_nonneg (hv i) hV.le
    · exact le_rfl

theorem mnlLaw_sum {N : ℕ} (v : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (S : Finset (Fin N)) :
    ∑ o, mnlLaw v S o = 1 := by
  have hV : 0 < 1 + ∑ j ∈ S, v j := by
    have := Finset.sum_nonneg (fun j (_ : j ∈ S) => hv j); linarith
  rw [Fintype.sum_option]
  simp only [mnlLaw]
  rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_div, ← add_div]
  exact div_self hV.ne'

theorem stepProb_nonneg {N : ℕ} (alg : Input N) (v : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i)
    (adv : Adversary N) {t : ℕ} (p : Fin t → Rec N) (x : Rec N) : 0 ≤ stepProb alg v adv p x := by
  simp only [stepProb]
  refine mul_nonneg (mul_nonneg ?_ ?_) ?_
  · split_ifs <;> positivity
  · split_ifs <;> norm_num
  · split_ifs
    · exact (adv.model_isChoice _ _ _).1 _
    · exact mnlLaw_nonneg v hv _ _

theorem sum_rec_aux {N : ℕ} (a : Fin N → ℝ) (φ : Bool) (q : Fin N → Option (Fin N) → ℝ)
    (hq : ∀ j, ∑ o, q j o = 1) :
    ∑ x : Rec N, a x.1 * (if x.2.1 = φ then 1 else 0) * q x.1 x.2.2 = ∑ j, a j := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Fintype.sum_prod_type]
  simp only
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [Fintype.sum_bool]
  cases φ <;> simp [hq j]

theorem stepProb_sum {N : ℕ} (alg : Input N) (v : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i)
    (adv : Adversary N) {t : ℕ} (p : Fin t → Rec N) : ∑ x, stepProb alg v adv p x ≤ 1 := by
  simp only [stepProb]
  set A' := nextActive alg (state alg p (epochOf N alg.K alg.T t))
  set φ := adv.outlier t (pubPast alg p)
  set st := state alg p (epochOf N alg.K alg.T t)
  refine (le_of_eq (sum_rec_aux (fun j => if j ∈ A' then 1 / (A'.card : ℝ) else 0) φ
    (fun j o => if φ = true then adv.model t (pubPast alg p) (alg.sel st.vhat st.A j) o
      else mnlLaw v (alg.sel st.vhat st.A j) o) (fun j => ?_))).trans ?_
  · split_ifs
    · exact (adv.model_isChoice _ _ _).2.1
    · exact mnlLaw_sum v hv _
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos (nextActive alg (state alg p (epochOf N alg.K alg.T t))).card with h | h
  · rw [h]; simp
  · rw [mul_one_div, div_self (by positivity)]

theorem pathLaw_nonneg {N : ℕ} (alg : Input N) (v : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i)
    (adv : Adversary N) (h : Fin alg.T → Rec N) : 0 ≤ pathLaw alg v adv h :=
  Finset.prod_nonneg (fun _ _ => stepProb_nonneg alg v hv adv _ _)

theorem pathLaw_sum {N : ℕ} (alg : Input N) (v : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i)
    (adv : Adversary N) : ∑ h, pathLaw alg v adv h ≤ 1 :=
  tree_sum (fun _ p x => stepProb alg v adv p x) (fun _ _ _ => stepProb_nonneg alg v hv adv _ _)
    (fun _ _ => stepProb_sum alg v hv adv _) alg.T

/-! ### Revenue bounds -/

theorem rev_nonneg {N : ℕ} (r w : Fin N → ℝ) (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1)
    (hw : ∀ i, 0 ≤ w i) (S : Finset (Fin N)) : 0 ≤ rev r w S := by
  unfold rev ChoiceCDLP.MNL.mnlObjective
  apply div_nonneg (Finset.sum_nonneg (fun i _ => mul_nonneg (hr i).1 (hw i)))
  have := Finset.sum_nonneg (fun j (_ : j ∈ S) => hw j); linarith

theorem rev_le_one {N : ℕ} (r w : Fin N → ℝ) (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1)
    (hw : ∀ i, 0 ≤ w i) (S : Finset (Fin N)) : rev r w S ≤ 1 := by
  unfold rev ChoiceCDLP.MNL.mnlObjective
  have h0 := Finset.sum_nonneg (fun j (_ : j ∈ S) => hw j)
  rw [div_le_one (by linarith)]
  have : ∑ j ∈ S, r j * w j ≤ ∑ j ∈ S, w j := Finset.sum_le_sum (fun i _ => by
    have := (hr i).2; have := hw i; nlinarith)
  linarith

theorem optRev_sub_le_one {N : ℕ} (r v : Fin N → ℝ) (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ i, 0 ≤ v i) (K : ℕ) (S : Finset (Fin N)) : optRev r v K - rev r v S ≤ 1 := by
  have h1 : optRev r v K ≤ 1 := Finset.sup'_le _ _ (fun S _ => rev_le_one r v hr hv S)
  have h2 := rev_nonneg r v hr hv S
  linarith

theorem deltaHat_nonneg (e : ℝ) (he : 0 ≤ e) (T K t n : ℕ) (hT : 1 ≤ T) :
    0 ≤ deltaHat e T K t n := by
  have hL : 0 ≤ Real.log (T : ℝ) := Real.log_nonneg (by exact_mod_cast hT)
  unfold deltaHat
  split_ifs
  · norm_num
  · have hm : 0 ≤ min 1 (e * T / t) := le_min zero_le_one (by positivity)
    have h3 : 0 ≤ 2 * (n : ℝ) * Real.log T / (3 * t) := by positivity
    have : 0 ≤ min 1 (e * T / t) / 2 + Real.sqrt (min 1 (e * T / t) * n * Real.log T / t) +
        2 * n * Real.log T / (3 * t) := by
      have := Real.sqrt_nonneg (min 1 (e * T / t) * n * Real.log T / t); linarith [hm]
    have := Real.sqrt_nonneg (K * n * Real.log T / t)
    positivity

theorem dhat_nonneg {N : ℕ} (alg : Input N) (he : 0 ≤ alg.epsBar) (hT : 1 ≤ alg.T) {t : ℕ}
    (p : Fin t → Rec N) (τ : ℕ) : 0 ≤ (state alg p τ).dhat := by
  cases τ with
  | zero => show (0 : ℝ) ≤ 1; norm_num
  | succ σ => exact deltaHat_nonneg _ he _ _ _ _ hT

/-! ### The regret split -/

open scoped Classical in
theorem regret_split {N : ℕ} (alg : Input N) (v : Fin N → ℝ) (adv : Adversary N)
    (hr : ∀ i, alg.r i ∈ Set.Icc (0 : ℝ) 1) (hv : ∀ i, v i ∈ Set.Icc (0 : ℝ) 1)
    (he : 0 ≤ alg.epsBar) (hT : 1 ≤ alg.T) (hT0 : 1 ≤ T0 N alg.K alg.T)
    (Sstar : Finset (Fin N)) (hopt : IsOptimal alg.r v alg.K Sstar) (M : ℝ)
    (hM : ∀ h : Fin alg.T → Rec N,
      4 * 1 * (epochLen N alg.K alg.T 0 : ℝ) +
        ∑ σ ∈ Finset.range (tau0 N alg.K alg.T),
          4 * (state alg h (σ + 1)).dhat * (epochLen N alg.K alg.T (σ + 1) : ℝ) ≤ M) :
    toteRegret alg v adv ≤ max M 0 +
      alg.T * prob alg v adv (fun h => ∃ τ : ℕ, τ ≤ tau0 N alg.K alg.T + 1 ∧
              ¬ Sstar ⊆ (state alg h τ).A) +
      alg.T * prob alg v adv (fun h =>
              (∀ τ : ℕ, τ ≤ tau0 N alg.K alg.T + 1 → Sstar ⊆ (state alg h τ).A) ∧
              ∃ τ : ℕ, τ ≤ tau0 N alg.K alg.T ∧
                ∃ i ∈ (state alg h (τ + 1)).A,
                  4 * (state alg h τ).dhat <
                    rev alg.r v Sstar - rev alg.r v (alg.sel (state alg h τ).vhat (state alg h τ).A i)) := by
  have hv0 : ∀ i, 0 ≤ v i := fun i => (hv i).1
  set L3 : (Fin alg.T → Rec N) → Prop := fun h => ∃ τ : ℕ, τ ≤ tau0 N alg.K alg.T + 1 ∧
              ¬ Sstar ⊆ (state alg h τ).A with hL3
  set L4 : (Fin alg.T → Rec N) → Prop := fun h =>
              (∀ τ : ℕ, τ ≤ tau0 N alg.K alg.T + 1 → Sstar ⊆ (state alg h τ).A) ∧
              ∃ τ : ℕ, τ ≤ tau0 N alg.K alg.T ∧
                ∃ i ∈ (state alg h (τ + 1)).A,
                  4 * (state alg h τ).dhat <
                    rev alg.r v Sstar - rev alg.r v (alg.sel (state alg h τ).vhat (state alg h τ).A i)
    with hL4
  -- the per-period regret is at most one
  have hle1 : ∀ h : Fin alg.T → Rec N, ∑ t : Fin alg.T,
      (optRev alg.r v alg.K - rev alg.r v (offeredAt alg h t)) ≤ alg.T := by
    intro h
    calc _ ≤ ∑ _t : Fin alg.T, (1 : ℝ) :=
          Finset.sum_le_sum (fun t _ => optRev_sub_le_one _ _ hr hv0 _ _)
      _ = alg.T := by simp
  -- on the good event
  have hgood : ∀ h : Fin alg.T → Rec N, pathLaw alg v adv h ≠ 0 → ¬ L3 h → ¬ L4 h →
      ∑ t : Fin alg.T, (optRev alg.r v alg.K - rev alg.r v (offeredAt alg h t)) ≤ M := by
    intro h hpos h3 h4
    have h3' : ∀ τ : ℕ, τ ≤ tau0 N alg.K alg.T + 1 → Sstar ⊆ (state alg h τ).A := by
      intro τ hτ; by_contra hc; exact h3 ⟨τ, hτ, hc⟩
    have h4' : ∀ τ : ℕ, τ ≤ tau0 N alg.K alg.T → ∀ i ∈ (state alg h (τ + 1)).A,
        rev alg.r v Sstar - rev alg.r v (alg.sel (state alg h τ).vhat (state alg h τ).A i) ≤
          4 * (state alg h τ).dhat := by
      intro τ hτ i hi; by_contra hc; push Not at hc; exact h4 ⟨h3', τ, hτ, i, hi, hc⟩
    have hterm : ∀ t : Fin alg.T, optRev alg.r v alg.K - rev alg.r v (offeredAt alg h t) ≤
        4 * (state alg h (epochOf N alg.K alg.T t.val)).dhat := by
      intro t
      have hstep : stepProb alg v adv (restrict h t.val t.isLt.le) (h t) ≠ 0 :=
        Finset.prod_ne_zero_iff.1 hpos t (Finset.mem_univ _)
      have hloc : state alg (restrict h t.val t.isLt.le) (epochOf N alg.K alg.T t.val) =
          state alg h (epochOf N alg.K alg.T t.val) :=
        state_restrict alg h t.isLt.le _ (epochOf_spec t.val).1
      have hmem : (h t).1 ∈ nextActive alg (state alg h (epochOf N alg.K alg.T t.val)) := by
        by_contra hn
        apply hstep
        simp only [stepProb]
        rw [hloc, if_neg hn]
        simp
      have hoff : offeredAt alg h t = alg.sel (state alg h (epochOf N alg.K alg.T t.val)).vhat
          (state alg h (epochOf N alg.K alg.T t.val)).A (h t).1 := by
        simp only [offeredAt, offered]
        rw [hloc]
      have hτ : epochOf N alg.K alg.T t.val ≤ tau0 N alg.K alg.T :=
        epochOf_mono (by have := t.isLt; omega)
      rw [hoff, ← hopt.2]
      exact h4' _ hτ _ hmem
    calc _ ≤ ∑ t : Fin alg.T, 4 * (state alg h (epochOf N alg.K alg.T t.val)).dhat :=
          Finset.sum_le_sum (fun t _ => hterm t)
      _ ≤ ∑ τ ∈ Finset.range (tau0 N alg.K alg.T + 1),
            4 * (state alg h τ).dhat * (epochLen N alg.K alg.T τ : ℝ) :=
          sum_epochs_le hT0 (fun τ => 4 * (state alg h τ).dhat)
            (fun τ => by have := dhat_nonneg alg he hT h τ; positivity)
      _ = 4 * 1 * (epochLen N alg.K alg.T 0 : ℝ) +
            ∑ σ ∈ Finset.range (tau0 N alg.K alg.T),
              4 * (state alg h (σ + 1)).dhat * (epochLen N alg.K alg.T (σ + 1) : ℝ) := by
          rw [Finset.sum_range_succ', add_comm]; rfl
      _ ≤ M := hM h
  -- pointwise bound
  have hpt : ∀ h : Fin alg.T → Rec N,
      pathLaw alg v adv h * ∑ t : Fin alg.T,
          (optRev alg.r v alg.K - rev alg.r v (offeredAt alg h t)) ≤
        max M 0 * pathLaw alg v adv h + alg.T * (if L3 h then pathLaw alg v adv h else 0) +
          alg.T * (if L4 h then pathLaw alg v adv h else 0) := by
    intro h
    have hp := pathLaw_nonneg alg v hv0 adv h
    have hTr : (0 : ℝ) ≤ alg.T := by positivity
    have hM0 : 0 ≤ max M 0 * pathLaw alg v adv h := mul_nonneg (le_max_right _ _) hp
    have hi3 : 0 ≤ (alg.T : ℝ) * (if L3 h then pathLaw alg v adv h else 0) := by
      split_ifs <;> positivity
    have hi4 : 0 ≤ (alg.T : ℝ) * (if L4 h then pathLaw alg v adv h else 0) := by
      split_ifs <;> positivity
    by_cases h0 : pathLaw alg v adv h = 0
    · have : pathLaw alg v adv h * ∑ t : Fin alg.T,
          (optRev alg.r v alg.K - rev alg.r v (offeredAt alg h t)) = 0 := by rw [h0, zero_mul]
      linarith
    by_cases h3 : L3 h
    · rw [if_pos h3]
      have := mul_le_mul_of_nonneg_left (hle1 h) hp
      linarith
    by_cases h4 : L4 h
    · rw [if_pos h4]
      have := mul_le_mul_of_nonneg_left (hle1 h) hp
      linarith
    · have := mul_le_mul_of_nonneg_left ((hgood h h0 h3 h4).trans (le_max_left M 0)) hp
      linarith
  unfold toteRegret prob
  calc _ ≤ ∑ h : Fin alg.T → Rec N, (max M 0 * pathLaw alg v adv h +
          alg.T * (if L3 h then pathLaw alg v adv h else 0) +
          alg.T * (if L4 h then pathLaw alg v adv h else 0)) := Finset.sum_le_sum (fun h _ => hpt h)
    _ = max M 0 * ∑ h, pathLaw alg v adv h +
          alg.T * ∑ h : Fin alg.T → Rec N, (if L3 h then pathLaw alg v adv h else 0) +
          alg.T * ∑ h : Fin alg.T → Rec N, (if L4 h then pathLaw alg v adv h else 0) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
          Finset.mul_sum]
    _ ≤ max M 0 + alg.T * ∑ h : Fin alg.T → Rec N, (if L3 h then pathLaw alg v adv h else 0) +
          alg.T * ∑ h : Fin alg.T → Rec N, (if L4 h then pathLaw alg v adv h else 0) := by
        have := mul_le_mul_of_nonneg_left (pathLaw_sum alg v hv0 adv) (le_max_right M 0)
        linarith
    _ ≤ _ := by apply le_of_eq; congr!

end OARed

open OARed in
theorem partA :
    ∃ C0 T1 : ℝ, 0 ≤ C0 ∧ ∀ (T N K : ℕ), T1 ≤ (T : ℝ) → 1 ≤ N → N ≤ T → 1 ≤ K →
      ∀ (r v : Fin N → ℝ), (∀ i, r i ∈ Set.Icc (0 : ℝ) 1) → (∀ i, v i ∈ Set.Icc (0 : ℝ) 1) →
      ∀ (eps epsBar : ℝ), 0 ≤ eps → eps ≤ epsBar →
      ∀ (adv : Adversary N), OutlierBudget adv T eps →
      ∀ (sel : (Fin N → ℝ) → Finset (Fin N) → Fin N → Finset (Fin N)), IsArgmaxSel r K sel →
        toteRegret (⟨T, epsBar, r, K, sel⟩ : Input N) v adv ≤
          C0 * (epsBar * K ^ 2 * T * Real.log T +
            (K ^ 2 * Real.sqrt epsBar + Real.sqrt K) * Real.sqrt (N * T * Real.log T ^ 3) +
            K ^ 2 * N * Real.log T ^ 2) := by
  obtain ⟨Cr, Tr, hrs⟩ := OutlierAssort.ActiveElim.regret_sum_bound
  obtain ⟨C3, T13, h3⟩ := OutlierAssort.ActiveElim.lemma_3
  obtain ⟨C4, T14, h4⟩ := OutlierAssort.ActiveElim.lemma_4
  refine ⟨max Cr 0 + max C3 0 + max C4 0, max (max Tr T13) (max T14 3), by positivity, ?_⟩
  intro T N K hT hN hNT hK r v hr hv eps epsBar heps hepsBar adv hadv sel hsel
  have hTr : Tr ≤ (T : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT13 : T13 ≤ (T : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT14 : T14 ≤ (T : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hT3 : (3 : ℝ) ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  have hTpos : (0 : ℝ) < T := by linarith
  have hT1 : 1 ≤ T := by exact_mod_cast (show (1 : ℝ) ≤ T by linarith)
  have hlog1 : 1 ≤ Real.log (T : ℝ) := by
    rw [Real.le_log_iff_exp_le hTpos]
    have := Real.exp_one_lt_d9
    linarith
  have hepsBar0 : 0 ≤ epsBar := heps.trans hepsBar
  have hT0 : 1 ≤ T0 N K T := by
    unfold T0
    apply Nat.one_le_iff_ne_zero.2
    apply Nat.pos_iff_ne_zero.1
    apply Nat.ceil_pos.2
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  -- an optimal assortment
  obtain ⟨Sstar, hSmem, hSeq⟩ :=
    Finset.exists_mem_eq_sup' (feasible_nonempty N K) (fun S => rev r v S)
  have hopt : IsOptimal r v K Sstar := by
    refine ⟨(Finset.mem_filter.1 hSmem).2, ?_⟩
    unfold optRev; rw [hSeq]
  set Stuff : ℝ := epsBar * K ^ 2 * T * Real.log T +
            (K ^ 2 * Real.sqrt epsBar + Real.sqrt K) * Real.sqrt (N * T * Real.log T ^ 3) +
            K ^ 2 * N * Real.log T ^ 2 with hStuff
  have hL0 : 0 ≤ Real.log (T : ℝ) := by linarith
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hlast : (N : ℝ) ≤ K ^ 2 * N * Real.log T ^ 2 := by
    have h1 : (1 : ℝ) ≤ (K : ℝ) ^ 2 := one_le_pow₀ hKr
    have h2 : (1 : ℝ) ≤ Real.log T ^ 2 := one_le_pow₀ hlog1
    have h3 : (1 : ℝ) ≤ (K : ℝ) ^ 2 * Real.log T ^ 2 := by nlinarith
    nlinarith
  have hStuff0 : K ^ 2 * N * Real.log T ^ 2 ≤ Stuff := by
    have a1 : 0 ≤ epsBar * K ^ 2 * T * Real.log T := by positivity
    have a2 : 0 ≤ (K ^ 2 * Real.sqrt epsBar + Real.sqrt K) * Real.sqrt (N * T * Real.log T ^ 3) := by
      positivity
    linarith
  -- the regret split
  have hsplit := regret_split (⟨T, epsBar, r, K, sel⟩ : Input N) v adv hr hv hepsBar0 hT1 hT0
    Sstar hopt (Cr * Stuff) (fun h => hrs T N K hTr hN hNT hK epsBar hepsBar0
      (fun σ => (state (⟨T, epsBar, r, K, sel⟩ : Input N) h (σ + 1)).A.card)
      (fun σ => (Finset.card_le_univ _).trans_eq (Fintype.card_fin N)))
  have hp3 := h3 T N K hT13 hN hK r v hr hv eps epsBar heps hepsBar adv hadv sel hsel Sstar hopt
  have hp4 := h4 T N K hT14 hN hK r v hr hv eps epsBar heps hepsBar adv hadv sel hsel Sstar hopt
  have htau : (tau0 N K T : ℝ) ≤ T := by
    have := (epochOf_spec (N := N) (K := K) (T := T) (T - 1)).2
    have : tau0 N K T ≤ T := by unfold tau0; omega
    exact_mod_cast this
  have hbad : ∀ C : ℝ, ∀ P : ℝ, P ≤ C * (tau0 N K T : ℝ) * N / (T : ℝ) ^ 2 →
      (T : ℝ) * P ≤ max C 0 * (K ^ 2 * N * Real.log T ^ 2) := by
    intro C P hP
    have hC : C ≤ max C 0 := le_max_left _ _
    have hC0 : 0 ≤ max C 0 := le_max_right _ _
    have e1 : (T : ℝ) * P ≤ (T : ℝ) * (max C 0 * (tau0 N K T : ℝ) * N / (T : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hTpos.le
      refine hP.trans ?_
      apply div_le_div_of_nonneg_right _ (by positivity)
      have : (0 : ℝ) ≤ (tau0 N K T : ℝ) * N := by positivity
      nlinarith
    have e2 : (T : ℝ) * (max C 0 * (tau0 N K T : ℝ) * N / (T : ℝ) ^ 2) =
        max C 0 * N * ((tau0 N K T : ℝ) / T) := by
      field_simp
    have e3 : (tau0 N K T : ℝ) / T ≤ 1 := (div_le_one hTpos).2 htau
    have e4 : max C 0 * N * ((tau0 N K T : ℝ) / T) ≤ max C 0 * N := by
      have : 0 ≤ max C 0 * (N : ℝ) := by positivity
      nlinarith
    have e5 : max C 0 * (N : ℝ) ≤ max C 0 * (K ^ 2 * N * Real.log T ^ 2) :=
      mul_le_mul_of_nonneg_left hlast hC0
    linarith
  have hb3 := hbad C3 _ hp3
  have hb4 := hbad C4 _ hp4
  have hM : max (Cr * Stuff) 0 ≤ max Cr 0 * Stuff := by
    apply max_le
    · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith [hStuff0, (by positivity : (0:ℝ) ≤ K ^ 2 * N * Real.log T ^ 2)])
    · have : (0 : ℝ) ≤ Stuff := le_trans (by positivity) hStuff0
      positivity
  have hfin : max Cr 0 * Stuff + max C3 0 * (K ^ 2 * N * Real.log T ^ 2) +
      max C4 0 * (K ^ 2 * N * Real.log T ^ 2) ≤ (max Cr 0 + max C3 0 + max C4 0) * Stuff := by
    have a := mul_le_mul_of_nonneg_left hStuff0 (le_max_right C3 0)
    have b := mul_le_mul_of_nonneg_left hStuff0 (le_max_right C4 0)
    have e : (max Cr 0 + max C3 0 + max C4 0) * Stuff =
        max Cr 0 * Stuff + max C3 0 * Stuff + max C4 0 * Stuff := by ring
    linarith
  exact hsplit.trans ((add_le_add (add_le_add hM hb3) hb4).trans hfin)

theorem solution :
    (∃ C0 T1 : ℝ, ∀ (T N K : ℕ), T1 ≤ (T : ℝ) → 1 ≤ N → N ≤ T → 1 ≤ K →
      ∀ (r v : Fin N → ℝ), (∀ i, r i ∈ Set.Icc (0 : ℝ) 1) → (∀ i, v i ∈ Set.Icc (0 : ℝ) 1) →
      ∀ (eps epsBar : ℝ), 0 ≤ eps → eps ≤ epsBar →
      ∀ (adv : Adversary N), OutlierBudget adv T eps →
      ∀ (sel : (Fin N → ℝ) → Finset (Fin N) → Fin N → Finset (Fin N)), IsArgmaxSel r K sel →
        toteRegret (⟨T, epsBar, r, K, sel⟩ : Input N) v adv ≤
          C0 * (epsBar * K ^ 2 * T * Real.log T +
            (K ^ 2 * Real.sqrt epsBar + Real.sqrt K) * Real.sqrt (N * T * Real.log T ^ 3) +
            K ^ 2 * N * Real.log T ^ 2)) ∧
    (∀ c1 c2 : ℝ, 0 < c1 → 0 < c2 →
      ∃ C T1 : ℝ, ∀ (T N K : ℕ), T1 ≤ (T : ℝ) → 1 ≤ N → N ≤ T → 1 ≤ K →
      ∀ (r v : Fin N → ℝ), (∀ i, r i ∈ Set.Icc (0 : ℝ) 1) → (∀ i, v i ∈ Set.Icc (0 : ℝ) 1) →
      ∀ (eps epsBar : ℝ), 0 ≤ eps → eps ≤ epsBar →
      ∀ (adv : Adversary N), OutlierBudget adv T eps →
      ∀ (sel : (Fin N → ℝ) → Finset (Fin N) → Fin N → Finset (Fin N)), IsArgmaxSel r K sel →
        epsBar ≤ c1 / (K : ℝ) ^ 3 → (K : ℝ) ^ 3 * N * Real.log T ≤ c2 * T →
        toteRegret (⟨T, epsBar, r, K, sel⟩ : Input N) v adv ≤
          C * (epsBar * K ^ 2 * T * Real.log T + Real.sqrt (K * N * T * Real.log T ^ 3))) := by
  obtain ⟨C0, T1, hC0, hA⟩ := partA
  refine ⟨⟨C0, T1, hA⟩, ?_⟩
  intro c1 c2 hc1 hc2
  refine ⟨C0 * (1 + Real.sqrt c1 + Real.sqrt c2), max T1 1, ?_⟩
  intro T N K hT hN hNT hK r v hr hv eps epsBar heps hepsBar adv hadv sel hsel hc1' hc2'
  have hreg := hA T N K (le_trans (le_max_left _ _) hT) hN hNT hK r v hr hv eps epsBar heps hepsBar
    adv hadv sel hsel
  have hT1 : (1 : ℝ) ≤ T := le_trans (le_max_right _ _) hT
  have hL : 0 ≤ Real.log (T : ℝ) := Real.log_nonneg hT1
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hK0 : (0 : ℝ) < K := by linarith
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hepsBar0 : 0 ≤ epsBar := heps.trans hepsBar
  set X := Real.sqrt (N * T * Real.log T ^ 3) with hX
  set Y := Real.sqrt (K * N * T * Real.log T ^ 3) with hY
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hY0 : 0 ≤ Y := Real.sqrt_nonneg _
  have hKX : Real.sqrt K * X = Y := by
    rw [hX, hY, ← Real.sqrt_mul (by positivity)]
    congr 1; ring
  have hsq : K ^ 2 * Real.sqrt epsBar ≤ Real.sqrt c1 * Real.sqrt K := by
    have e1 : Real.sqrt epsBar ≤ Real.sqrt (c1 / (K : ℝ) ^ 3) := Real.sqrt_le_sqrt hc1'
    have e2 : (K : ℝ) ^ 2 * Real.sqrt (c1 / (K : ℝ) ^ 3) = Real.sqrt c1 * Real.sqrt K := by
      rw [← Real.sqrt_mul hc1.le]
      rw [show (K : ℝ) ^ 2 = Real.sqrt ((K : ℝ) ^ 4) by
        rw [show (K : ℝ) ^ 4 = ((K : ℝ) ^ 2) ^ 2 by ring]
        exact (Real.sqrt_sq (by positivity)).symm]
      rw [← Real.sqrt_mul (by positivity)]
      congr 1
      field_simp
    calc K ^ 2 * Real.sqrt epsBar ≤ K ^ 2 * Real.sqrt (c1 / (K : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_left e1 (by positivity)
      _ = _ := e2
  have hterm2 : (K ^ 2 * Real.sqrt epsBar) * X ≤ Real.sqrt c1 * Y := by
    calc (K ^ 2 * Real.sqrt epsBar) * X ≤ (Real.sqrt c1 * Real.sqrt K) * X :=
          mul_le_mul_of_nonneg_right hsq hX0
      _ = Real.sqrt c1 * Y := by rw [mul_assoc, hKX]
  have hterm3 : (K : ℝ) ^ 2 * N * Real.log T ^ 2 ≤ Real.sqrt c2 * Y := by
    rw [hY, ← Real.sqrt_mul hc2.le]
    apply Real.le_sqrt_of_sq_le
    have e : ((K : ℝ) ^ 2 * N * Real.log T ^ 2) ^ 2 =
        ((K : ℝ) ^ 3 * N * Real.log T) * (K * N * Real.log T ^ 3) := by ring
    rw [e]
    have : c2 * (K * N * T * Real.log T ^ 3) = (c2 * T) * (K * N * Real.log T ^ 3) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hc2' (by positivity)
  have hA0 : 0 ≤ epsBar * K ^ 2 * T * Real.log T := by positivity
  have hsc1 := Real.sqrt_nonneg c1
  have hsc2 := Real.sqrt_nonneg c2
  have hinner : epsBar * K ^ 2 * T * Real.log T + (K ^ 2 * Real.sqrt epsBar + Real.sqrt K) * X +
      K ^ 2 * N * Real.log T ^ 2 ≤
      (1 + Real.sqrt c1 + Real.sqrt c2) * (epsBar * K ^ 2 * T * Real.log T + Y) := by
    have : (K ^ 2 * Real.sqrt epsBar + Real.sqrt K) * X = (K ^ 2 * Real.sqrt epsBar) * X + Y := by
      rw [add_mul, hKX]
    rw [this]
    have e : (1 + Real.sqrt c1 + Real.sqrt c2) * (epsBar * K ^ 2 * T * Real.log T + Y) =
        epsBar * K ^ 2 * T * Real.log T + Y + Real.sqrt c1 * (epsBar * K ^ 2 * T * Real.log T) +
          Real.sqrt c1 * Y + Real.sqrt c2 * (epsBar * K ^ 2 * T * Real.log T) + Real.sqrt c2 * Y := by
      ring
    rw [e]
    have f1 := mul_nonneg hsc1 hA0
    have f2 := mul_nonneg hsc2 hA0
    linarith
  calc _ ≤ _ := hreg
    _ ≤ C0 * ((1 + Real.sqrt c1 + Real.sqrt c2) * (epsBar * K ^ 2 * T * Real.log T + Y)) :=
        mul_le_mul_of_nonneg_left hinner hC0
    _ = _ := by ring
