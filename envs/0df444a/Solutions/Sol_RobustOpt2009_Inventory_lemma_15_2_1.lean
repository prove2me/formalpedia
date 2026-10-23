-- Prove2me | solution 1 for RobustOpt2009.Inventory.lemma_15_2_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T02:34:52.487828+00:00
-- url     : https://prove2.me/submissions/b2f37a08-0de8-4d38-a081-793878878b61

import Mathlib

open scoped BigOperators

namespace X8Inv

lemma x8_sum_coe {ι : Type*} (u : Finset ι) (a : ι → ℝ) :
    ∑ i ∈ u, ((a i : ℝ) : EReal) = ((∑ i ∈ u, a i : ℝ) : EReal) := by
  classical
  induction u using Finset.induction_on with
  | empty => simp
  | insert i u hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, ih, EReal.coe_add]

lemma x8_sum_ne_bot {ι : Type*} (u : Finset ι) (g : ι → EReal) (hb : ∀ i ∈ u, g i ≠ ⊥) :
    ∑ i ∈ u, g i ≠ ⊥ := by
  classical
  induction u using Finset.induction_on with
  | empty => simp
  | insert i u hi ih =>
    rw [Finset.sum_insert hi]
    exact EReal.add_ne_bot_iff.2 ⟨hb i (Finset.mem_insert_self _ _),
      ih (fun j hj => hb j (Finset.mem_insert_of_mem hj))⟩

lemma x8_ne_top {ι : Type*} [DecidableEq ι] (u : Finset ι) (g : ι → EReal)
    (hb : ∀ i ∈ u, g i ≠ ⊥) (E : ℝ) (hE : ∑ i ∈ u, g i ≤ (E : EReal)) :
    ∀ i ∈ u, g i ≠ ⊤ := by
  intro i hi htop
  rw [← Finset.add_sum_erase _ _ hi, htop,
    EReal.top_add_of_ne_bot (x8_sum_ne_bot _ _ (fun j hj => hb j (Finset.mem_of_mem_erase hj)))]
    at hE
  exact absurd hE (by simp)

lemma x8_sum_eq {ι : Type*} (u : Finset ι) (g : ι → EReal)
    (hb : ∀ i ∈ u, g i ≠ ⊥) (ht : ∀ i ∈ u, g i ≠ ⊤) :
    ∑ i ∈ u, g i = ((∑ i ∈ u, (g i).toReal : ℝ) : EReal) := by
  rw [← x8_sum_coe]
  exact Finset.sum_congr rfl (fun i hi => (EReal.coe_toReal (ht i hi) (hb i hi)).symm)

variable {n m k : ℕ → ℕ} (T : ℕ)
    (A : (t : ℕ) → (Fin (m t) → ℝ) →ₗ[ℝ] (Fin (k t) → ℝ))
    (B : (t : ℕ) → ((j : Fin (t + 1)) → Fin (n j.val) → ℝ) →ₗ[ℝ]
      (Fin (k (t + 1)) → ℝ))
    (C : (t : ℕ) → (Fin (m t) → ℝ) →ₗ[ℝ] (Fin (k (t + 1)) → ℝ))
    (b : (t : ℕ) → Fin (k t) → ℝ)
    (f : (t : ℕ) → (Fin (m t) → ℝ) → EReal) (R : ℝ)

def feas (F : (t : ℕ) → Set (Fin (n t) → ℝ)) (E : ℝ) : Prop :=
        ∃ S : (t : ℕ) → ((j : Fin t) → Fin (n j.val) → ℝ) → (Fin (m t) → ℝ),
        ∀ d : (j : Fin (T + 1)) → Fin (n j.val) → ℝ,
        (∀ j, d j ∈ F j.val) →
          (∑ t : Fin (T + 1), f (t.val + 1)
            (S (t.val + 1) (fun j => d ⟨j.val,
              lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt t.isLt)⟩))) ≤ (E : EReal) ∧
          b 1 ≤ A 1 (S 1 (fun j => d ⟨j.val,
            lt_of_lt_of_le j.isLt (Nat.succ_le_succ (Nat.zero_le T))⟩)) ∧
          (∀ t : ℕ, ∀ _ht : 1 ≤ t, ∀ hT : t ≤ T,
            B t (fun j => d ⟨j.val, lt_of_lt_of_le j.isLt (Nat.succ_le_succ hT)⟩) +
              C t (S t (fun j => d ⟨j.val,
                lt_of_lt_of_le j.isLt (Nat.le_trans hT (Nat.le_succ T))⟩)) + b (t + 1) ≤
              A (t + 1) (S (t + 1) (fun j => d ⟨j.val,
                lt_of_lt_of_le j.isLt (Nat.succ_le_succ hT)⟩))) ∧
          (∀ t : ℕ, ∀ _ht : 1 ≤ t, ∀ hT : t ≤ T,
            ‖S t (fun j => d ⟨j.val,
              lt_of_lt_of_le j.isLt (Nat.le_trans hT (Nat.le_succ T))⟩)‖ ≤ R)

/-- averaging inequality: termwise `≤` survives nonnegative combinations -/
lemma x8_avg_le {ι M : Type*} [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
    [Module ℝ M] [PosSMulMono ℝ M] (u : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ u, 0 ≤ w i)
    (a c : ι → M) (h : ∀ i ∈ u, a i ≤ c i) :
    ∑ i ∈ u, w i • a i ≤ ∑ i ∈ u, w i • c i :=
  Finset.sum_le_sum (fun i hi => smul_le_smul_of_nonneg_left (h i hi) (hw i hi))

end X8Inv


open scoped BigOperators

namespace X8Inv

variable {n m k : ℕ → ℕ} (T : ℕ)
    (A : (t : ℕ) → (Fin (m t) → ℝ) →ₗ[ℝ] (Fin (k t) → ℝ))
    (B : (t : ℕ) → ((j : Fin (t + 1)) → Fin (n j.val) → ℝ) →ₗ[ℝ]
      (Fin (k (t + 1)) → ℝ))
    (C : (t : ℕ) → (Fin (m t) → ℝ) →ₗ[ℝ] (Fin (k (t + 1)) → ℝ))
    (b : (t : ℕ) → Fin (k t) → ℝ)
    (f : (t : ℕ) → (Fin (m t) → ℝ) → EReal) (R : ℝ)

/-- a full path is the average of its updates at coordinate `i` -/
lemma x8_path_avg {N : ℕ} {β : Fin N → Type*} [∀ j, AddCommGroup (β j)] [∀ j, Module ℝ (β j)]
    (d : (j : Fin N) → β j) (i : Fin N) (s : Finset (β i)) (w : β i → ℝ)
    (h1 : ∑ v ∈ s, w v = 1) (hx : ∑ v ∈ s, w v • v = d i) :
    d = ∑ v ∈ s, w v • Function.update d i v := by
  funext j
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply]
  by_cases hj : j = i
  · subst hj
    simp only [Function.update_self]
    exact hx.symm
  · simp only [Function.update_of_ne hj]
    rw [← Finset.sum_smul, h1, one_smul]

lemma x8_step (F F' : (t : ℕ) → Set (Fin (n t) → ℝ)) (t : ℕ) (ht : t ≤ T)
    (hF : ∀ j, j ≠ t → F' j ⊆ F j)
    (hH : ∀ x ∈ F' t, ∃ s : Finset (Fin (n t) → ℝ), (↑s : Set _) ⊆ F t ∧
      x ∈ convexHull ℝ (↑s : Set (Fin (n t) → ℝ)))
    (hf : ∀ t, 1 ≤ t → t ≤ T + 1 →
      (∀ x, f t x ≠ ⊥) ∧ ConvexOn ℝ {x | f t x ≠ ⊤} (fun x => (f t x).toReal))
    (E : ℝ) (hE : feas T A B C b f R F E) : feas T A B C b f R F' E := by
  classical
  have hch : ∀ x : Fin (n t) → ℝ, ∃ (s : Finset (Fin (n t) → ℝ)) (w : (Fin (n t) → ℝ) → ℝ),
      x ∈ F' t → ((↑s : Set _) ⊆ F t ∧ (∀ y ∈ s, 0 ≤ w y) ∧ ∑ y ∈ s, w y = 1 ∧
        ∑ y ∈ s, w y • y = x) := by
    intro x
    by_cases hx : x ∈ F' t
    · obtain ⟨s, hs, hxs⟩ := hH x hx
      obtain ⟨w, hw0, hw1, hwx⟩ := Finset.mem_convexHull'.1 hxs
      exact ⟨s, w, fun _ => ⟨hs, hw0, hw1, hwx⟩⟩
    · exact ⟨∅, fun _ => 0, fun h => absurd h hx⟩
  choose sx wx hsw using hch
  obtain ⟨S, hS⟩ := hE
  let S' : (s : ℕ) → ((j : Fin s) → Fin (n j.val) → ℝ) → (Fin (m s) → ℝ) :=
    fun s p => if h : t < s then
      ∑ v ∈ sx (p ⟨t, h⟩), wx (p ⟨t, h⟩) v • S s (Function.update p ⟨t, h⟩ v)
      else S s p
  refine ⟨S', fun d hd => ?_⟩
  have ht' : t < T + 1 := Nat.lt_succ_of_le ht
  set i : Fin (T + 1) := ⟨t, ht'⟩ with hi
  set x := d i with hxdef
  obtain ⟨hsF, hw0, hw1, hwx⟩ := hsw x (hd i)
  set s := sx x
  set w := wx x
  -- the updated paths are feasible for `F`
  have hdv : ∀ v ∈ s, ∀ j, Function.update d i v j ∈ F j.val := by
    intro v hv j
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self]
      exact hsF hv
    · rw [Function.update_of_ne hj]
      refine hF _ ?_ (hd j)
      intro h
      exact hj (Fin.ext h)
  have hdavg := x8_path_avg d i s w hw1 hwx
  -- prefixes
  have hpre : ∀ (s' : ℕ) (hs : s' ≤ T + 1),
      S' s' (fun j : Fin s' => d ⟨j.val, lt_of_lt_of_le j.isLt hs⟩) =
        ∑ v ∈ s, w v • S s' (fun j : Fin s' =>
          Function.update d i v ⟨j.val, lt_of_lt_of_le j.isLt hs⟩) := by
    intro s' hs
    by_cases h : t < s'
    · simp only [S', dif_pos h]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      congr 2
      funext j
      by_cases hj : j = ⟨t, h⟩
      · subst hj
        simp only [Function.update_self]
        exact (Function.update_self i v d).symm
      · have hj' : (⟨j.val, lt_of_lt_of_le j.isLt hs⟩ : Fin (T + 1)) ≠ i := by
          intro h'
          apply hj
          ext
          simpa [hi] using congrArg Fin.val h'
        rw [Function.update_of_ne hj, Function.update_of_ne hj']
    · simp only [S', dif_neg h]
      have : ∀ v, (fun j : Fin s' => Function.update d i v ⟨j.val, lt_of_lt_of_le j.isLt hs⟩) =
          (fun j : Fin s' => d ⟨j.val, lt_of_lt_of_le j.isLt hs⟩) := by
        intro v
        funext j
        have hj' : (⟨j.val, lt_of_lt_of_le j.isLt hs⟩ : Fin (T + 1)) ≠ i := by
          intro h'
          have := congrArg Fin.val h'
          simp [hi] at this
          omega
        rw [Function.update_of_ne hj']
      simp only [this]
      rw [← Finset.sum_smul, hw1, one_smul]
  have hpd : ∀ (s' : ℕ) (hs : s' ≤ T + 1),
      (fun j : Fin s' => d ⟨j.val, lt_of_lt_of_le j.isLt hs⟩) =
        ∑ v ∈ s, w v • (fun j : Fin s' =>
          Function.update d i v ⟨j.val, lt_of_lt_of_le j.isLt hs⟩) := by
    intro s' hs
    funext j
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply]
    conv_lhs => rw [hdavg]
    rw [Finset.sum_apply]
    rfl
  have hSv := fun v (hv : v ∈ s) => hS _ (hdv v hv)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- cost
    have hbot : ∀ t₁ : Fin (T + 1), ∀ z, f (t₁.val + 1) z ≠ ⊥ := fun t₁ z =>
      (hf _ (by omega) (by omega)).1 z
    have hvtop : ∀ v ∈ s, ∀ t₁ : Fin (T + 1), f (t₁.val + 1) (S (t₁.val + 1)
        (fun j : Fin (t₁.val + 1) => Function.update d i v
          ⟨j.val, lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt t₁.isLt)⟩)) ≠ ⊤ := by
      intro v hv t₁
      exact x8_ne_top Finset.univ _ (fun t₂ _ => hbot t₂ _) E (hSv v hv).1 t₁ (Finset.mem_univ _)
    have hvE : ∀ v ∈ s, ∑ t₁ : Fin (T + 1), (f (t₁.val + 1) (S (t₁.val + 1)
        (fun j : Fin (t₁.val + 1) => Function.update d i v
          ⟨j.val, lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt t₁.isLt)⟩))).toReal ≤ E := by
      intro v hv
      have h := (hSv v hv).1
      rw [x8_sum_eq _ _ (fun t₂ _ => hbot t₂ _) (fun t₂ _ => hvtop v hv t₂)] at h
      exact EReal.coe_le_coe_iff.1 h
    have hterm : ∀ t₁ : Fin (T + 1),
        f (t₁.val + 1) (S' (t₁.val + 1) (fun j : Fin (t₁.val + 1) =>
          d ⟨j.val, lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt t₁.isLt)⟩)) ≠ ⊤ ∧
        (f (t₁.val + 1) (S' (t₁.val + 1) (fun j : Fin (t₁.val + 1) =>
          d ⟨j.val, lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt t₁.isLt)⟩))).toReal ≤
        ∑ v ∈ s, w v * (f (t₁.val + 1) (S (t₁.val + 1)
          (fun j : Fin (t₁.val + 1) => Function.update d i v
            ⟨j.val, lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt t₁.isLt)⟩))).toReal := by
      intro t₁
      have hc := (hf (t₁.val + 1) (by omega) (by omega)).2
      rw [hpre (t₁.val + 1) (Nat.succ_le_of_lt t₁.isLt)]
      have hmem : ∀ v ∈ s, S (t₁.val + 1)
          (fun j : Fin (t₁.val + 1) => Function.update d i v
            ⟨j.val, lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt t₁.isLt)⟩) ∈
            {z | f (t₁.val + 1) z ≠ ⊤} := fun v hv => hvtop v hv t₁
      refine ⟨hc.1.sum_mem hw0 hw1 hmem, ?_⟩
      have := hc.map_sum_le hw0 hw1 hmem
      simpa only [smul_eq_mul] using this
    rw [x8_sum_eq _ _ (fun t₂ _ => hbot t₂ _) (fun t₂ _ => (hterm t₂).1)]
    refine EReal.coe_le_coe_iff.2 ?_
    calc _ ≤ ∑ t₁ : Fin (T + 1), ∑ v ∈ s, w v * (f (t₁.val + 1) (S (t₁.val + 1)
          (fun j : Fin (t₁.val + 1) => Function.update d i v
            ⟨j.val, lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt t₁.isLt)⟩))).toReal :=
          Finset.sum_le_sum (fun t₁ _ => (hterm t₁).2)
      _ = ∑ v ∈ s, w v * ∑ t₁ : Fin (T + 1), (f (t₁.val + 1) (S (t₁.val + 1)
          (fun j : Fin (t₁.val + 1) => Function.update d i v
            ⟨j.val, lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt t₁.isLt)⟩))).toReal := by
          rw [Finset.sum_comm]
          simp only [Finset.mul_sum]
      _ ≤ ∑ v ∈ s, w v * E :=
          Finset.sum_le_sum (fun v hv => mul_le_mul_of_nonneg_left (hvE v hv) (hw0 v hv))
      _ = E := by rw [← Finset.sum_mul, hw1, one_mul]
  · rw [hpre 1 (Nat.succ_le_succ (Nat.zero_le T)), map_sum]
    simp only [map_smul]
    calc b 1 = ∑ v ∈ s, w v • b 1 := by rw [← Finset.sum_smul, hw1, one_smul]
      _ ≤ _ := x8_avg_le s w hw0 _ _ (fun v hv => (hSv v hv).2.1)
  · intro t₁ h1 hT
    rw [hpre (t₁ + 1) (Nat.succ_le_succ hT), hpre t₁ (Nat.le_trans hT (Nat.le_succ T)),
      hpd (t₁ + 1) (Nat.succ_le_succ hT), map_sum, map_sum, map_sum]
    simp only [map_smul]
    calc _ = ∑ v ∈ s, w v • (B t₁ (fun j : Fin (t₁ + 1) =>
          Function.update d i v ⟨j.val, lt_of_lt_of_le j.isLt (Nat.succ_le_succ hT)⟩) +
          C t₁ (S t₁ (fun j : Fin t₁ => Function.update d i v
            ⟨j.val, lt_of_lt_of_le j.isLt (Nat.le_trans hT (Nat.le_succ T))⟩)) + b (t₁ + 1)) := by
          simp only [smul_add, Finset.sum_add_distrib]
          rw [← Finset.sum_smul, hw1, one_smul]
      _ ≤ _ := x8_avg_le s w hw0 _ _ (fun v hv => (hSv v hv).2.2.1 t₁ h1 hT)
  · intro t₁ h1 hT
    rw [hpre t₁ (Nat.le_trans hT (Nat.le_succ T))]
    calc _ ≤ ∑ v ∈ s, ‖w v • S t₁ (fun j : Fin t₁ => Function.update d i v
            ⟨j.val, lt_of_lt_of_le j.isLt (Nat.le_trans hT (Nat.le_succ T))⟩)‖ := norm_sum_le _ _
      _ ≤ ∑ v ∈ s, w v * R := by
          refine Finset.sum_le_sum (fun v hv => ?_)
          rw [norm_smul, Real.norm_of_nonneg (hw0 v hv)]
          exact mul_le_mul_of_nonneg_left ((hSv v hv).2.2.2 t₁ h1 hT) (hw0 v hv)
      _ = R := by rw [← Finset.sum_mul, hw1, one_mul]

end X8Inv


open scoped BigOperators

namespace X8Inv

variable {n m k : ℕ → ℕ} (T : ℕ)
    (A : (t : ℕ) → (Fin (m t) → ℝ) →ₗ[ℝ] (Fin (k t) → ℝ))
    (B : (t : ℕ) → ((j : Fin (t + 1)) → Fin (n j.val) → ℝ) →ₗ[ℝ]
      (Fin (k (t + 1)) → ℝ))
    (C : (t : ℕ) → (Fin (m t) → ℝ) →ₗ[ℝ] (Fin (k (t + 1)) → ℝ))
    (b : (t : ℕ) → Fin (k t) → ℝ)
    (f : (t : ℕ) → (Fin (m t) → ℝ) → EReal) (R : ℝ)

lemma x8_mono (F F' : (t : ℕ) → Set (Fin (n t) → ℝ)) (h : ∀ j, j ≤ T → F' j ⊆ F j)
    (E : ℝ) (hE : feas T A B C b f R F E) : feas T A B C b f R F' E := by
  obtain ⟨S, hS⟩ := hE
  exact ⟨S, fun d hd => hS d (fun j => h j.val (Nat.lt_succ_iff.1 j.isLt) (hd j))⟩

lemma x8_km {N : ℕ} (D : Set (Fin N → ℝ)) (V : Finset (Fin N → ℝ))
    (hD : D = convexHull ℝ (V : Set (Fin N → ℝ))) :
    (D.extremePoints ℝ).Finite ∧ D ⊆ convexHull ℝ (D.extremePoints ℝ) := by
  have hfin : (D.extremePoints ℝ).Finite := by
    rw [hD]
    exact V.finite_toSet.subset extremePoints_convexHull_subset
  refine ⟨hfin, ?_⟩
  have hc : IsCompact D := by rw [hD]; exact V.finite_toSet.isCompact_convexHull ℝ
  have hv : Convex ℝ D := by rw [hD]; exact convex_convexHull ℝ _
  have := closure_convexHull_extremePoints hc hv
  rw [(hfin.isCompact_convexHull ℝ).isClosed.closure_eq] at this
  rw [this]

lemma x8_main (D : (t : ℕ) → Set (Fin (n t) → ℝ))
    (hD : ∀ t, t ≤ T → ∃ V : Finset (Fin (n t) → ℝ),
      V.Nonempty ∧ D t = convexHull ℝ (V : Set (Fin (n t) → ℝ)))
    (hf : ∀ t, 1 ≤ t → t ≤ T + 1 →
      (∀ x, f t x ≠ ⊥) ∧ ConvexOn ℝ {x | f t x ≠ ⊤} (fun x => (f t x).toReal))
    (E : ℝ) (hE : feas T A B C b f R (fun t => (D t).extremePoints ℝ) E) :
    feas T A B C b f R D E := by
  classical
  let Fi : ℕ → (t : ℕ) → Set (Fin (n t) → ℝ) := fun i j =>
    if j < i then D j else (D j).extremePoints ℝ
  have hstep : ∀ i, i ≤ T + 1 → feas T A B C b f R (Fi i) E := by
    intro i
    induction i with
    | zero =>
      intro _
      exact x8_mono T A B C b f R _ _ (fun j _ => by simp [Fi]) E hE
    | succ i ih =>
      intro hi
      have hiT : i ≤ T := by omega
      refine x8_step T A B C b f R (Fi i) (Fi (i + 1)) i hiT ?_ ?_ hf E (ih (by omega))
      · intro j hj
        simp only [Fi]
        by_cases h1 : j < i
        · rw [if_pos h1, if_pos (by omega)]
        · rw [if_neg h1, if_neg (by omega)]
      · intro x hx
        simp only [Fi, lt_irrefl, if_false, Nat.lt_succ_self, if_true] at hx ⊢
        obtain ⟨V, _, hV⟩ := hD i hiT
        obtain ⟨hfin, hsub⟩ := x8_km (D i) V hV
        exact ⟨hfin.toFinset, by simp, by rw [Set.Finite.coe_toFinset]; exact hsub hx⟩
  refine x8_mono T A B C b f R _ _ (fun j hj => ?_) E (hstep (T + 1) le_rfl)
  simp only [Fi, if_pos (Nat.lt_succ_of_le hj)]
  exact le_rfl

end X8Inv

open X8Inv in
theorem solution {n m k : ℕ → ℕ} (T : ℕ)
    (A : (t : ℕ) → (Fin (m t) → ℝ) →ₗ[ℝ] (Fin (k t) → ℝ))
    (B : (t : ℕ) → ((j : Fin (t + 1)) → Fin (n j.val) → ℝ) →ₗ[ℝ]
      (Fin (k (t + 1)) → ℝ))
    (C : (t : ℕ) → (Fin (m t) → ℝ) →ₗ[ℝ] (Fin (k (t + 1)) → ℝ))
    (b : (t : ℕ) → Fin (k t) → ℝ)
    (f : (t : ℕ) → (Fin (m t) → ℝ) → EReal) (R : ℝ)
    (D : (t : ℕ) → Set (Fin (n t) → ℝ))
    (hD : ∀ t, t ≤ T → ∃ V : Finset (Fin (n t) → ℝ),
      V.Nonempty ∧ D t = convexHull ℝ (V : Set (Fin (n t) → ℝ)))
    (hf : ∀ t, 1 ≤ t → t ≤ T + 1 →
      (∀ x, f t x ≠ ⊥) ∧ LowerSemicontinuous (f t) ∧
      ConvexOn ℝ {x | f t x ≠ ⊤} (fun x => (f t x).toReal) ∧
      ∃ (q : ℕ) (G : Matrix (Fin q) (Fin (m t)) ℝ) (g : Fin q → ℝ),
        {x | f t x ≠ ⊤} = {x | G.mulVec x ≤ g}) :
    let value := fun (F : (t : ℕ) → Set (Fin (n t) → ℝ)) =>
      sInf {v : EReal | ∃ E : ℝ, v = (E : EReal) ∧
        ∃ S : (t : ℕ) → ((j : Fin t) → Fin (n j.val) → ℝ) → (Fin (m t) → ℝ),
        ∀ d : (j : Fin (T + 1)) → Fin (n j.val) → ℝ,
        (∀ j, d j ∈ F j.val) →
          (∑ t : Fin (T + 1), f (t.val + 1)
            (S (t.val + 1) (fun j => d ⟨j.val,
              lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt t.isLt)⟩))) ≤ (E : EReal) ∧
          b 1 ≤ A 1 (S 1 (fun j => d ⟨j.val,
            lt_of_lt_of_le j.isLt (Nat.succ_le_succ (Nat.zero_le T))⟩)) ∧
          (∀ t : ℕ, ∀ _ht : 1 ≤ t, ∀ hT : t ≤ T,
            B t (fun j => d ⟨j.val, lt_of_lt_of_le j.isLt (Nat.succ_le_succ hT)⟩) +
              C t (S t (fun j => d ⟨j.val,
                lt_of_lt_of_le j.isLt (Nat.le_trans hT (Nat.le_succ T))⟩)) + b (t + 1) ≤
              A (t + 1) (S (t + 1) (fun j => d ⟨j.val,
                lt_of_lt_of_le j.isLt (Nat.succ_le_succ hT)⟩))) ∧
          (∀ t : ℕ, ∀ _ht : 1 ≤ t, ∀ hT : t ≤ T,
            ‖S t (fun j => d ⟨j.val,
              lt_of_lt_of_le j.isLt (Nat.le_trans hT (Nat.le_succ T))⟩)‖ ≤ R)}
    value D = value (fun t => (D t).extremePoints ℝ) := by
  intro value
  have hf' : ∀ t, 1 ≤ t → t ≤ T + 1 →
      (∀ x, f t x ≠ ⊥) ∧ ConvexOn ℝ {x | f t x ≠ ⊤} (fun x => (f t x).toReal) :=
    fun t h1 h2 => ⟨(hf t h1 h2).1, (hf t h1 h2).2.2.1⟩
  show sInf {v : EReal | ∃ E : ℝ, v = (E : EReal) ∧ feas T A B C b f R D E} =
    sInf {v : EReal | ∃ E : ℝ, v = (E : EReal) ∧
      feas T A B C b f R (fun t => (D t).extremePoints ℝ) E}
  apply le_antisymm
  · apply sInf_le_sInf
    rintro v ⟨E, rfl, hE⟩
    exact ⟨E, rfl, x8_main T A B C b f R D hD hf' E hE⟩
  · apply sInf_le_sInf
    rintro v ⟨E, rfl, hE⟩
    exact ⟨E, rfl, x8_mono T A B C b f R _ _ (fun j _ => extremePoints_subset) E hE⟩
