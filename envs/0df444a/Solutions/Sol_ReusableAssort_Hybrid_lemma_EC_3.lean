-- Prove2me | solution 1 for ReusableAssort.Hybrid.lemma_EC_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T06:55:47.812018+00:00
-- url     : https://prove2.me/submissions/70290b96-2393-4a60-a8fe-1ae18c86c9d0

import Mathlib
import Definitions.Def_ReusableAssort_Hybrid_Algorithms
import Theorems.Thm_ReusableAssort_Hybrid_proposition_3

section Markov

variable {α : Type} [Fintype α] [DecidableEq α] {N : ℕ}

/-- Summing out one coordinate. -/
private lemma sum_split (G : (Fin N → α) → ℝ) (j : Fin N) (x0 : α) :
    ∑ v, G v = ∑ v, (if v j = x0 then 1 else 0) * ∑ x, G (Function.update v j x) := by
  have hx : ∀ x, ∑ v, (if v j = x0 then (1 : ℝ) else 0) * G (Function.update v j x)
      = ∑ w, (if w j = x then (1 : ℝ) else 0) * G w := by
    intro x
    simp_rw [ite_mul, one_mul, zero_mul]
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    refine Finset.sum_nbij' (fun v => Function.update v j x) (fun w => Function.update w j x0)
      ?_ ?_ ?_ ?_ ?_
    · intro v _; simp
    · intro w _; simp
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      simp only [Function.update_idem]
      rw [← hv, Function.update_eq_self]
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      simp only [Function.update_idem]
      rw [← hw, Function.update_eq_self]
    · intro v _; rfl
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [hx]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp [Finset.sum_ite_eq]

/-- `f` depends only on the coordinates `< m`. -/
private def DepLt (f : (Fin N → α) → ℝ) (m : ℕ) : Prop :=
  ∀ v w : Fin N → α, (∀ k : Fin N, k.1 < m → v k = w k) → f v = f w

private lemma DepLt.mono {f : (Fin N → α) → ℝ} {m m' : ℕ} (h : DepLt f m) (hm : m ≤ m') :
    DepLt f m' := fun v w hvw => h v w fun k hk => hvw k (by omega)

/-- The truncated path measure: kernels at steps `< m`, point masses at `x0` afterwards. -/
private noncomputable def Ptr (K : (Fin N → α) → Fin N → ℝ) (x0 : α) (m : ℕ)
    (v : Fin N → α) : ℝ :=
  ∏ k, if k.1 < m then K v k else (if v k = x0 then 1 else 0)

/-- One step: integrating step `m` given the prefix. -/
private lemma step_eq (K : (Fin N → α) → Fin N → ℝ) (x0 : α)
    (hK : ∀ k : Fin N, DepLt (fun v => K v k) (k.1 + 1))
    (m : Fin N) (g : (Fin N → α) → ℝ) :
    ∑ v, Ptr K x0 (m.1 + 1) v * g v
      = ∑ v, Ptr K x0 m.1 v * ∑ x, K (Function.update v m x) m * g (Function.update v m x) := by
  rw [sum_split _ m x0]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hrest : ∀ x, ∏ k ∈ Finset.univ.erase m,
      (if k.1 < m.1 + 1 then K (Function.update v m x) k
        else (if (Function.update v m x) k = x0 then 1 else 0))
      = ∏ k ∈ Finset.univ.erase m,
      (if k.1 < m.1 then K v k else (if v k = x0 then 1 else 0)) := by
    intro x
    refine Finset.prod_congr rfl fun k hk => ?_
    have hkm : k ≠ m := Finset.ne_of_mem_erase hk
    have hkm' : k.1 ≠ m.1 := fun h => hkm (Fin.ext h)
    by_cases hlt : k.1 < m.1
    · rw [if_pos (by omega), if_pos hlt]
      apply hK k
      intro j hj
      have : j ≠ m := fun h => by subst h; omega
      simp [Function.update_of_ne this]
    · rw [if_neg (by omega), if_neg hlt, Function.update_of_ne hkm]
  unfold Ptr
  simp_rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ m)]
  simp only [hrest, lt_add_iff_pos_right, Nat.lt_irrefl, if_false, zero_lt_one, if_true,
    Function.update_self]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

private lemma step_const (K : (Fin N → α) → Fin N → ℝ) (x0 : α)
    (hK : ∀ k : Fin N, DepLt (fun v => K v k) (k.1 + 1))
    (hK1 : ∀ v (k : Fin N), ∑ x, K (Function.update v k x) k = 1)
    (m : Fin N) (g : (Fin N → α) → ℝ) (hg : DepLt g m.1) :
    ∑ v, Ptr K x0 (m.1 + 1) v * g v = ∑ v, Ptr K x0 m.1 v * g v := by
  rw [step_eq K x0 hK m g]
  refine Finset.sum_congr rfl fun v _ => ?_
  congr 1
  have : ∀ x, g (Function.update v m x) = g v := by
    intro x
    apply hg
    intro k hk
    have : k ≠ m := fun h => by subst h; omega
    simp [Function.update_of_ne this]
  simp_rw [this, ← Finset.sum_mul, hK1, one_mul]

/-- Truncation: the full path measure integrates `f` (depending on coordinates `< m`) like the
measure truncated at `m`. -/
private lemma trunc (K : (Fin N → α) → Fin N → ℝ) (x0 : α)
    (hK : ∀ k : Fin N, DepLt (fun v => K v k) (k.1 + 1))
    (hK1 : ∀ v (k : Fin N), ∑ x, K (Function.update v k x) k = 1)
    (m : ℕ) (hm : m ≤ N) (f : (Fin N → α) → ℝ) (hf : DepLt f m) :
    ∑ v, (∏ k, K v k) * f v = ∑ v, Ptr K x0 m v * f v := by
  have hfull : ∀ v, (∏ k, K v k) = Ptr K x0 N v := by
    intro v; unfold Ptr
    exact Finset.prod_congr rfl fun k _ => by rw [if_pos k.2]
  simp_rw [hfull]
  have H : ∀ j, m ≤ j → j ≤ N → ∑ v, Ptr K x0 j v * f v = ∑ v, Ptr K x0 m v * f v := by
    intro j hmj
    induction j, hmj using Nat.le_induction with
    | base => intro _; rfl
    | succ j hmj ih =>
      intro hjN
      rw [← ih (by omega)]
      exact step_const K x0 hK hK1 ⟨j, by omega⟩ f (hf.mono hmj)
  exact H N hm le_rfl

private lemma Ptr_zero_sum (K : (Fin N → α) → Fin N → ℝ) (x0 : α) :
    ∑ v, Ptr K x0 0 v = 1 := by
  unfold Ptr
  simp only [Nat.not_lt_zero, if_false]
  rw [← Fintype.prod_sum (fun (_ : Fin N) (x : α) => if x = x0 then (1 : ℝ) else 0)]
  simp

end Markov

open ReusableAssort.Hybrid

section Spec

variable {n T : ℕ} {Z : Type} [Fintype Z] [DecidableEq Z]

private lemma phi_mono' (I : Instance n T Z) (hI : I.Assumptions) (z : Z) :
    ∀ S ∈ I.feas, ∀ S' ⊆ S, ∀ i ∈ S', I.phi z S i ≤ I.phi z S' i := by
  have key : ∀ D : Finset (Fin n), ∀ S' : Finset (Fin n), S' ∪ D ∈ I.feas →
      ∀ i ∈ S', I.phi z (S' ∪ D) i ≤ I.phi z S' i := by
    intro D
    induction D using Finset.induction_on with
    | empty => intro S' _ i _; simp
    | insert a D haD ih =>
      intro S' hfe i hi
      rw [Finset.union_insert] at hfe ⊢
      have hfe' : S' ∪ D ∈ I.feas := hI.down_closed _ hfe _ (Finset.subset_insert _ _)
      by_cases ha : a ∈ S' ∪ D
      · rw [Finset.insert_eq_of_mem ha]
        exact ih S' hfe' i hi
      · have hai : a ≠ i := by
          rintro rfl; exact ha (Finset.mem_union_left _ hi)
        exact (hI.weak_subst z _ hfe' i a hai hfe).trans (ih S' hfe' i hi)
  intro S hS S' hS' i hi
  have := key (S \ S') S' (by rwa [Finset.union_sdiff_of_subset hS']) i hi
  rwa [Finset.union_sdiff_of_subset hS'] at this

private lemma onHand_congr (I : Instance n T Z) (t₀ : ℕ) (ret : Fin n → ℕ → ℕ)
    (v w : Fin (T + 1 - t₀) → Step n T Z) (i : Fin n) (k : ℕ)
    (h : ∀ j : Fin (T + 1 - t₀), j.1 < k → v j = w j) :
    onHand I t₀ ret v i k = onHand I t₀ ret w i k := by
  have hf : Finset.univ.filter (fun j : Fin (T + 1 - t₀) =>
        j.1 < k ∧ (v j).2.2.2.2.1 = some i ∧ k < j.1 + ((v j).2.2.2.2.2 : ℕ))
      = Finset.univ.filter (fun j : Fin (T + 1 - t₀) =>
        j.1 < k ∧ (w j).2.2.2.2.1 = some i ∧ k < j.1 + ((w j).2.2.2.2.2 : ℕ)) := by
    apply Finset.filter_congr
    intro j _
    constructor
    · rintro ⟨hj, h2⟩; exact ⟨hj, by rwa [← h j hj]⟩
    · rintro ⟨hj, h2⟩; exact ⟨hj, by rwa [h j hj]⟩
  unfold onHand
  rw [hf]

/-- Choice probabilities of the consumer. -/
private noncomputable def Cf (I : Instance n T Z) (z : Z) (St : Finset (Fin n)) :
    Option (Fin n) → ℝ
  | some i => if i ∈ St then I.phi z St i else 0
  | none => 1 - ∑ i ∈ St, I.phi z St i

/-- Rental-duration probabilities. -/
private noncomputable def Gf (I : Instance n T Z) (z : Z) : Option (Fin n) → Fin (T + 1) → ℝ
  | some i, d => I.g z i (d : ℕ)
  | none, d => if (d : ℕ) = 0 then 1 else 0

/-- Discarding probabilities (independent keeps with probabilities `a`). -/
private noncomputable def Df (a : Fin n → ℝ) (Sh Sb : Finset (Fin n)) : ℝ :=
  (if Sb ⊆ Sh then 1 else 0) * (∏ i ∈ Sb, a i) * ∏ i ∈ Sh \ Sb, (1 - a i)

/-- The law of one step at time `t` given keep probabilities `a z i`. -/
private noncomputable def kstep (I : Instance n T Z) (y : ℕ → Z → Finset (Fin n) → ℝ)
    (t : ℕ) (a : Z → Fin n → ℝ) (x : Step n T Z) : ℝ :=
  I.F t x.1 * y t x.1 x.2.1 * (if x.2.1 ∈ I.feas then 1 else 0)
    * Df (a x.1) x.2.1 x.2.2.1
    * subAssort (I.phi x.1) x.2.2.1 (fun i => I.phi x.1 x.2.1 i) x.2.2.2.1
    * Cf I x.1 x.2.2.2.1 x.2.2.2.2.1
    * Gf I x.1 x.2.2.2.2.1 x.2.2.2.2.2

private noncomputable def aOf (I : Instance n T Z) (rule : Fin n → Rule Z) (t₀ : ℕ)
    (ret : Fin n → ℕ → ℕ) (v : Fin (T + 1 - t₀) → Step n T Z) (k : ℕ) : Z → Fin n → ℝ :=
  fun z i => if onHand I t₀ ret v i k = 0 then 0 else keep I i (rule i) (t₀ + k) z

private lemma kernel_update (I : Instance n T Z) (y : ℕ → Z → Finset (Fin n) → ℝ)
    (rule : Fin n → Rule Z) (t₀ : ℕ) (ret : Fin n → ℕ → ℕ)
    (v : Fin (T + 1 - t₀) → Step n T Z) (k : Fin (T + 1 - t₀)) (x : Step n T Z) :
    kernel I y rule t₀ ret (Function.update v k x) k
      = kstep I y (t₀ + k.1) (aOf I rule t₀ ret v k.1) x := by
  have hon : ∀ i, onHand I t₀ ret (Function.update v k x) i k.1 = onHand I t₀ ret v i k.1 := by
    intro i
    apply onHand_congr
    intro j hj
    have : j ≠ k := fun h => by subst h; omega
    simp [Function.update_of_ne this]
  simp only [kernel, kstep, Function.update_self, hon, aOf, Df]
  obtain ⟨z, Sh, Sb, St, ch, d⟩ := x
  cases ch <;> rfl

private lemma kernel_dep (I : Instance n T Z) (y : ℕ → Z → Finset (Fin n) → ℝ)
    (rule : Fin n → Rule Z) (t₀ : ℕ) (ret : Fin n → ℕ → ℕ) (k : Fin (T + 1 - t₀)) :
    DepLt (fun v => kernel I y rule t₀ ret v k) (k.1 + 1) := by
  intro v w hvw
  have hk : v k = w k := hvw k (by omega)
  have hon : ∀ i, onHand I t₀ ret v i k.1 = onHand I t₀ ret w i k.1 :=
    fun i => onHand_congr I t₀ ret v w i k.1 fun j hj => hvw j (by omega)
  simp only [kernel, hk, hon]

private lemma Gf_sum (I : Instance n T Z) (hI : I.Assumptions) (z : Z) (ch : Option (Fin n)) :
    ∑ d : Fin (T + 1), Gf I z ch d = 1 := by
  cases ch with
  | none =>
    simp only [Gf]
    rw [Finset.sum_eq_single (0 : Fin (T + 1))]
    · simp
    · intro d _ hd
      rw [if_neg]
      intro h; exact hd (Fin.ext h)
    · intro h; exact absurd (Finset.mem_univ _) h
  | some i =>
    simp only [Gf]
    rw [Fin.sum_univ_eq_sum_range (fun d => I.g z i d), Finset.sum_range_succ',
      hI.g_zero, add_zero, ← hI.g_sum z i]
    rw [Finset.range_eq_Ico, Finset.sum_Ico_add' (fun d => I.g z i d)]
    rfl

private lemma Cf_sum (I : Instance n T Z) (z : Z) (St : Finset (Fin n)) :
    ∑ ch : Option (Fin n), Cf I z St ch = 1 := by
  rw [Fintype.sum_option]
  simp only [Cf]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  ring

private lemma Cf_rev (I : Instance n T Z) (z : Z) (St : Finset (Fin n)) (i : Fin n) (c : ℝ) :
    ∑ ch : Option (Fin n), Cf I z St ch * (if ch = some i then c else 0)
      = if i ∈ St then I.phi z St i * c else 0 := by
  rw [Fintype.sum_option]
  simp only [Cf, reduceCtorEq, if_false, mul_zero, zero_add, Option.some.injEq]
  rw [Finset.sum_eq_single i]
  · simp only [if_true]; split_ifs <;> ring
  · intro j _ hj; rw [if_neg hj, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma Df_sum (a : Fin n → ℝ) (Sh : Finset (Fin n)) : ∑ Sb, Df a Sh Sb = 1 := by
  simp only [Df, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have : Finset.univ.filter (fun Sb : Finset (Fin n) => Sb ⊆ Sh) = Sh.powerset := by
    ext Sb; simp
  rw [this, ← Finset.prod_add]
  simp

private lemma Df_rev (a : Fin n → ℝ) (Sh : Finset (Fin n)) (i : Fin n) (c : ℝ) :
    ∑ Sb, Df a Sh Sb * (if i ∈ Sb then c else 0) = if i ∈ Sh then a i * c else 0 := by
  simp only [Df, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have : Finset.univ.filter (fun Sb : Finset (Fin n) => Sb ⊆ Sh) = Sh.powerset := by
    ext Sb; simp
  rw [this]
  split_ifs with hi
  · rw [← Finset.insert_erase hi, Finset.sum_powerset_insert (Finset.notMem_erase i Sh)]
    have h1 : ∑ t ∈ (Sh.erase i).powerset,
        (∏ j ∈ t, a j) * (∏ j ∈ insert i (Sh.erase i) \ t, (1 - a j)) *
          (if i ∈ t then c else 0) = 0 := by
      refine Finset.sum_eq_zero fun t ht => ?_
      have : i ∉ t := fun h => Finset.notMem_erase i Sh (Finset.mem_powerset.mp ht h)
      rw [if_neg this, mul_zero]
    rw [h1, zero_add]
    have h2 : ∀ t ∈ (Sh.erase i).powerset,
        (∏ j ∈ insert i t, a j) * (∏ j ∈ insert i (Sh.erase i) \ insert i t, (1 - a j)) *
          (if i ∈ insert i t then c else 0)
        = a i * c * ((∏ j ∈ t, a j) * ∏ j ∈ Sh.erase i \ t, (1 - a j)) := by
      intro t ht
      have hit : i ∉ t := fun h => Finset.notMem_erase i Sh (Finset.mem_powerset.mp ht h)
      rw [Finset.prod_insert hit, if_pos (Finset.mem_insert_self i t)]
      have : insert i (Sh.erase i) \ insert i t = Sh.erase i \ t := by
        ext j; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro ⟨h1, h2⟩; push Not at h2; tauto
        · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨Or.inr ⟨h1, h2⟩, by tauto⟩
      rw [this]; ring
    rw [Finset.sum_congr rfl h2, ← Finset.mul_sum, ← Finset.prod_add]
    simp
  · refine Finset.sum_eq_zero fun t ht => ?_
    have : i ∉ t := fun h => hi (Finset.mem_powerset.mp ht h)
    rw [if_neg this, mul_zero]

private lemma sub_sum (I : Instance n T Z) (hI : I.Assumptions) (z : Z)
    {Sh Sb : Finset (Fin n)} (hSh : Sh ∈ I.feas) (hSb : Sb ⊆ Sh) :
    ∑ St, subAssort (I.phi z) Sb (fun i => I.phi z Sh i) St = 1 := by
  have hSbf : Sb ∈ I.feas := hI.down_closed Sh hSh Sb hSb
  have P := proposition_3 (I.phi z) I.feas (hI.phi_empty z) (hI.weak_subst z) hI.down_closed
    (hI.phi_nonneg z) (hI.phi_support z) (hI.phi_sum_le z) Sb hSbf (fun i => I.phi z Sh i)
    (fun i hi => ⟨hI.phi_nonneg z Sh hSh i, phi_mono' I hI z Sh hSh Sb hSb i hi⟩)
  rw [← P.2.2.1]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro U _ hU
  by_contra h
  exact hU (Finset.mem_powerset.mpr (P.1 U h))

private lemma sub_rev (I : Instance n T Z) (hI : I.Assumptions) (z : Z)
    {Sh Sb : Finset (Fin n)} (hSh : Sh ∈ I.feas) (hSb : Sb ⊆ Sh) (i : Fin n) (c : ℝ) :
    ∑ St, subAssort (I.phi z) Sb (fun i => I.phi z Sh i) St
        * (if i ∈ St then I.phi z St i * c else 0)
      = if i ∈ Sb then I.phi z Sh i * c else 0 := by
  have hSbf : Sb ∈ I.feas := hI.down_closed Sh hSh Sb hSb
  have P := proposition_3 (I.phi z) I.feas (hI.phi_empty z) (hI.weak_subst z) hI.down_closed
    (hI.phi_nonneg z) (hI.phi_support z) (hI.phi_sum_le z) Sb hSbf (fun i => I.phi z Sh i)
    (fun i hi => ⟨hI.phi_nonneg z Sh hSh i, phi_mono' I hI z Sh hSh Sb hSb i hi⟩)
  have hres : ∑ St, subAssort (I.phi z) Sb (fun i => I.phi z Sh i) St
        * (if i ∈ St then I.phi z St i * c else 0)
      = ∑ St ∈ Sb.powerset, subAssort (I.phi z) Sb (fun i => I.phi z Sh i) St
        * I.phi z St i * c := by
    symm
    rw [Finset.sum_subset (Finset.subset_univ Sb.powerset)]
    · refine Finset.sum_congr rfl fun St _ => ?_
      by_cases hSt : subAssort (I.phi z) Sb (fun i => I.phi z Sh i) St = 0
      · rw [hSt]; ring
      have hStf : St ∈ I.feas := hI.down_closed Sb hSbf St (P.1 St hSt)
      split_ifs with hi
      · ring
      · rw [hI.phi_support z St hStf i hi]; ring
    · intro U _ hU
      have : subAssort (I.phi z) Sb (fun i => I.phi z Sh i) U = 0 := by
        by_contra h; exact hU (Finset.mem_powerset.mpr (P.1 U h))
      rw [this]; ring
  rw [hres, ← Finset.sum_mul]
  split_ifs with hi
  · rw [P.2.2.2 i hi]
  · rw [Finset.sum_eq_zero, zero_mul]
    intro U hU
    have hUs := Finset.mem_powerset.mp hU
    rw [hI.phi_support z U (hI.down_closed Sb hSbf U hUs) i (fun h => hi (hUs h)), mul_zero]

private lemma kstep_sum (I : Instance n T Z) (hI : I.Assumptions)
    (y : ℕ → Z → Finset (Fin n) → ℝ) (hN : Normalized I y) {t : ℕ}
    (ht : t ∈ Finset.Icc 1 T) (a : Z → Fin n → ℝ) :
    ∑ x, kstep I y t a x = 1 := by
  simp only [kstep, Fintype.sum_prod_type]
  have hd : ∀ z Sh Sb St ch, ∑ d : Fin (T + 1), I.F t z * y t z Sh
      * (if Sh ∈ I.feas then 1 else 0) * Df (a z) Sh Sb
      * subAssort (I.phi z) Sb (fun i => I.phi z Sh i) St * Cf I z St ch * Gf I z ch d
      = I.F t z * y t z Sh * (if Sh ∈ I.feas then 1 else 0) * Df (a z) Sh Sb
      * subAssort (I.phi z) Sb (fun i => I.phi z Sh i) St * Cf I z St ch := by
    intro z Sh Sb St ch
    rw [← Finset.mul_sum, Gf_sum I hI, mul_one]
  have hc : ∀ z Sh Sb St, ∑ ch, I.F t z * y t z Sh
      * (if Sh ∈ I.feas then 1 else 0) * Df (a z) Sh Sb
      * subAssort (I.phi z) Sb (fun i => I.phi z Sh i) St * Cf I z St ch
      = I.F t z * y t z Sh * (if Sh ∈ I.feas then 1 else 0) * Df (a z) Sh Sb
      * subAssort (I.phi z) Sb (fun i => I.phi z Sh i) St := by
    intro z Sh Sb St
    rw [← Finset.mul_sum, Cf_sum, mul_one]
  simp only [hd, hc]
  have h1 : ∀ z Sh, ∑ Sb, I.F t z * y t z Sh * (if Sh ∈ I.feas then 1 else 0) * Df (a z) Sh Sb *
      ∑ St, subAssort (I.phi z) Sb (fun i => I.phi z Sh i) St
      = I.F t z * y t z Sh * (if Sh ∈ I.feas then 1 else 0) := by
    intro z Sh
    have : ∀ Sb, I.F t z * y t z Sh * (if Sh ∈ I.feas then 1 else 0) * Df (a z) Sh Sb *
        ∑ St, subAssort (I.phi z) Sb (fun i => I.phi z Sh i) St
        = I.F t z * y t z Sh * (if Sh ∈ I.feas then 1 else 0) * Df (a z) Sh Sb := by
      intro Sb
      by_cases hSh : Sh ∈ I.feas
      · by_cases hSb : Sb ⊆ Sh
        · rw [sub_sum I hI z hSh hSb, mul_one]
        · simp [Df, hSb]
      · simp [hSh]
    simp only [this]
    rw [← Finset.mul_sum, Df_sum, mul_one]
  have h1' : ∀ z Sh, ∑ Sb, ∑ St, I.F t z * y t z Sh * (if Sh ∈ I.feas then 1 else 0)
      * Df (a z) Sh Sb * subAssort (I.phi z) Sb (fun i => I.phi z Sh i) St
      = I.F t z * y t z Sh * (if Sh ∈ I.feas then 1 else 0) := by
    intro z Sh
    refine Eq.trans (Finset.sum_congr rfl fun Sb _ => ?_) (h1 z Sh)
    rw [Finset.mul_sum]
  simp only [h1']
  have hz : ∀ z, ∑ Sh, I.F t z * y t z Sh * (if Sh ∈ I.feas then 1 else 0) = I.F t z := by
    intro z
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.mul_sum, hN t ht z, mul_one]
  simp only [hz]
  exact hI.F_sum t ht

private lemma kstep_rev (I : Instance n T Z) (hI : I.Assumptions)
    (y : ℕ → Z → Finset (Fin n) → ℝ) {t : ℕ} (a : Z → Fin n → ℝ) (i : Fin n) :
    ∑ x, kstep I y t a x * (if x.2.2.2.2.1 = some i then I.r x.1 i else 0)
      = ∑ z, a z i * ∑ S ∈ I.feas, I.F t z * I.r z i * I.phi z S i * y t z S := by
  simp only [kstep, Fintype.sum_prod_type]
  have hd : ∀ z Sh Sb St ch, ∑ d : Fin (T + 1),
      I.F t z * y t z Sh * (if Sh ∈ I.feas then 1 else 0) * Df (a z) Sh Sb
        * subAssort (I.phi z) Sb (fun i => I.phi z Sh i) St * Cf I z St ch * Gf I z ch d
        * (if ch = some i then I.r z i else 0)
      = I.F t z * y t z Sh * (if Sh ∈ I.feas then 1 else 0) * Df (a z) Sh Sb
        * subAssort (I.phi z) Sb (fun i => I.phi z Sh i) St
        * (Cf I z St ch * (if ch = some i then I.r z i else 0)) := by
    intro z Sh Sb St ch
    have : ∀ d : Fin (T + 1), I.F t z * y t z Sh * (if Sh ∈ I.feas then 1 else 0)
        * Df (a z) Sh Sb * subAssort (I.phi z) Sb (fun i => I.phi z Sh i) St * Cf I z St ch
        * Gf I z ch d * (if ch = some i then I.r z i else 0)
        = (I.F t z * y t z Sh * (if Sh ∈ I.feas then 1 else 0) * Df (a z) Sh Sb
        * subAssort (I.phi z) Sb (fun i => I.phi z Sh i) St
        * (Cf I z St ch * (if ch = some i then I.r z i else 0))) * Gf I z ch d := by
      intro d; ring
    simp only [this, ← Finset.mul_sum, Gf_sum I hI, mul_one]
  simp only [hd, ← Finset.mul_sum, Cf_rev]
  have hst : ∀ z Sh Sb, ∑ St, I.F t z * y t z Sh * (if Sh ∈ I.feas then 1 else 0)
      * Df (a z) Sh Sb * subAssort (I.phi z) Sb (fun i => I.phi z Sh i) St
        * (if i ∈ St then I.phi z St i * I.r z i else 0)
      = I.F t z * y t z Sh * (if Sh ∈ I.feas then 1 else 0) * (Df (a z) Sh Sb *
        (if i ∈ Sb then I.phi z Sh i * I.r z i else 0)) := by
    intro z Sh Sb
    have e : ∑ St, I.F t z * y t z Sh * (if Sh ∈ I.feas then 1 else 0)
      * Df (a z) Sh Sb * subAssort (I.phi z) Sb (fun i => I.phi z Sh i) St
        * (if i ∈ St then I.phi z St i * I.r z i else 0)
        = I.F t z * y t z Sh * (if Sh ∈ I.feas then 1 else 0) * Df (a z) Sh Sb *
          ∑ St, subAssort (I.phi z) Sb (fun i => I.phi z Sh i) St
            * (if i ∈ St then I.phi z St i * I.r z i else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun St _ => by ring
    rw [e]
    by_cases hSh : Sh ∈ I.feas
    · by_cases hSb : Sb ⊆ Sh
      · rw [sub_rev I hI z hSh hSb]; ring
      · simp [Df, hSb]
    · simp [hSh]
  simp only [hst]
  have hsb : ∀ z Sh, ∑ Sb, I.F t z * y t z Sh * (if Sh ∈ I.feas then 1 else 0) * (Df (a z) Sh Sb *
        (if i ∈ Sb then I.phi z Sh i * I.r z i else 0))
      = I.F t z * y t z Sh * (if Sh ∈ I.feas then 1 else 0) *
        (if i ∈ Sh then a z i * (I.phi z Sh i * I.r z i) else 0) := by
    intro z Sh
    rw [← Finset.mul_sum, Df_rev]
  simp only [hsb]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.mul_sum]
  rw [← Finset.sum_subset (Finset.subset_univ I.feas)]
  · refine Finset.sum_congr rfl fun S hS => ?_
    rw [if_pos hS]
    split_ifs with hiS
    · ring
    · rw [hI.phi_support z S hS i hiS]; ring
  · intro S _ hS
    rw [if_neg hS]; ring

end Spec

section Spec2

variable {n T : ℕ} {Z : Type} [Fintype Z] [DecidableEq Z]

private lemma kstep_nonneg (I : Instance n T Z) (hI : I.Assumptions)
    (y : ℕ → Z → Finset (Fin n) → ℝ) (hy : LPFeasible I y) {t : ℕ}
    (ht : t ∈ Finset.Icc 1 T) (a : Z → Fin n → ℝ) (ha : ∀ z j, 0 ≤ a z j ∧ a z j ≤ 1)
    (x : Step n T Z) : 0 ≤ kstep I y t a x := by
  obtain ⟨z, Sh, Sb, St, ch, d⟩ := x
  simp only [kstep]
  by_cases hSh : Sh ∈ I.feas
  swap
  · simp [hSh]
  by_cases hSb : Sb ⊆ Sh
  swap
  · simp [Df, hSb]
  have hSbf : Sb ∈ I.feas := hI.down_closed Sh hSh Sb hSb
  have P := proposition_3 (I.phi z) I.feas (hI.phi_empty z) (hI.weak_subst z) hI.down_closed
    (hI.phi_nonneg z) (hI.phi_support z) (hI.phi_sum_le z) Sb hSbf (fun i => I.phi z Sh i)
    (fun i hi => ⟨hI.phi_nonneg z Sh hSh i, phi_mono' I hI z Sh hSh Sb hSb i hi⟩)
  have hD : 0 ≤ Df (a z) Sh Sb := by
    simp only [Df, if_pos hSb, one_mul]
    exact mul_nonneg (Finset.prod_nonneg fun j _ => (ha z j).1)
      (Finset.prod_nonneg fun j _ => by linarith [(ha z j).2])
  have hsub := P.2.1 St
  by_cases hs0 : subAssort (I.phi z) Sb (fun i => I.phi z Sh i) St = 0
  · rw [hs0]; simp
  have hStf : St ∈ I.feas := hI.down_closed Sb hSbf St (P.1 St hs0)
  have hC : 0 ≤ Cf I z St ch := by
    cases ch with
    | none => simp only [Cf]; linarith [hI.phi_sum_le z St hStf]
    | some j => simp only [Cf]; split_ifs
                · exact hI.phi_nonneg z St hStf j
                · exact le_refl _
  have hG : 0 ≤ Gf I z ch d := by
    cases ch with
    | none => simp only [Gf]; split_ifs <;> norm_num
    | some j => exact hI.g_nonneg z j _
  have := hy.1 t ht z Sh hSh
  have := hI.F_nonneg t z
  rw [if_pos hSh, mul_one]
  positivity

private lemma aOf_bounds (I : Instance n T Z) (rule : Fin n → Rule Z)
    (hrule : ∀ j, (rule j).Valid) (t₀ : ℕ) (ret : Fin n → ℕ → ℕ)
    (v : Fin (T + 1 - t₀) → Step n T Z) (k : ℕ) :
    ∀ z j, 0 ≤ aOf I rule t₀ ret v k z j ∧ aOf I rule t₀ ret v k z j ≤ 1 := by
  intro z j
  simp only [aOf]
  split_ifs
  · norm_num
  · have hv := hrule j
    revert hv
    cases rule j with
    | random γ => intro hv; simp only [keep]; exact ⟨by linarith [hv.2], by linarith [hv.1]⟩
    | threshold P => intro _; simp only [keep]; split_ifs <;> norm_num

private lemma kernel_nonneg (I : Instance n T Z) (hI : I.Assumptions)
    (y : ℕ → Z → Finset (Fin n) → ℝ) (hy : LPFeasible I y)
    (rule : Fin n → Rule Z) (hrule : ∀ j, (rule j).Valid) (t₀ : ℕ) (ht₀ : 1 ≤ t₀)
    (ret : Fin n → ℕ → ℕ) (v : Fin (T + 1 - t₀) → Step n T Z) (k : Fin (T + 1 - t₀)) :
    0 ≤ kernel I y rule t₀ ret v k := by
  have h := kernel_update I y rule t₀ ret v k (v k)
  rw [Function.update_eq_self] at h
  rw [h]
  exact kstep_nonneg I hI y hy (Finset.mem_Icc.mpr ⟨by omega, by have := k.2; omega⟩) _
    (aOf_bounds I rule hrule t₀ ret v k.1) _

private lemma kstep_wrev (I : Instance n T Z) (hI : I.Assumptions)
    (y : ℕ → Z → Finset (Fin n) → ℝ) {t : ℕ} (a : Z → Fin n → ℝ) (i : Fin n)
    (W : Z → ℕ → ℝ) :
    ∑ x, kstep I y t a x * (if x.2.2.2.2.1 = some i then W x.1 (x.2.2.2.2.2 : ℕ) else 0)
      = ∑ z, a z i * ∑ S ∈ I.feas, I.F t z * (∑ d : Fin (T + 1), I.g z i d * W z d)
          * I.phi z S i * y t z S := by
  simp only [kstep, Fintype.sum_prod_type]
  have hd : ∀ z Sh Sb St ch, ∑ d : Fin (T + 1),
      I.F t z * y t z Sh * (if Sh ∈ I.feas then 1 else 0) * Df (a z) Sh Sb
        * subAssort (I.phi z) Sb (fun i => I.phi z Sh i) St * Cf I z St ch * Gf I z ch d
        * (if ch = some i then W z d else 0)
      = I.F t z * y t z Sh * (if Sh ∈ I.feas then 1 else 0) * Df (a z) Sh Sb
        * subAssort (I.phi z) Sb (fun i => I.phi z Sh i) St
        * (Cf I z St ch * (if ch = some i then ∑ d : Fin (T + 1), I.g z i d * W z d else 0)) := by
    intro z Sh Sb St ch
    cases ch with
    | none => simp
    | some j =>
      by_cases hj : j = i
      · subst hj
        simp only [Gf, if_true, Finset.mul_sum]
        exact Finset.sum_congr rfl fun d _ => by ring
      · have : (some j : Option (Fin n)) ≠ some i := fun h => hj (Option.some.inj h)
        simp only [if_neg this, mul_zero, Finset.sum_const_zero]
  simp only [hd]
  have hc : ∀ z Sh Sb St, ∑ ch, I.F t z * y t z Sh * (if Sh ∈ I.feas then 1 else 0)
      * Df (a z) Sh Sb * subAssort (I.phi z) Sb (fun i => I.phi z Sh i) St
      * (Cf I z St ch * (if ch = some i then ∑ d : Fin (T + 1), I.g z i d * W z d else 0))
      = I.F t z * y t z Sh * (if Sh ∈ I.feas then 1 else 0)
      * Df (a z) Sh Sb * subAssort (I.phi z) Sb (fun i => I.phi z Sh i) St
      * (if i ∈ St then I.phi z St i * ∑ d : Fin (T + 1), I.g z i d * W z d else 0) := by
    intro z Sh Sb St
    rw [← Finset.mul_sum, Cf_rev]
  simp only [hc]
  have hst : ∀ z Sh Sb, ∑ St, I.F t z * y t z Sh * (if Sh ∈ I.feas then 1 else 0)
      * Df (a z) Sh Sb * subAssort (I.phi z) Sb (fun i => I.phi z Sh i) St
        * (if i ∈ St then I.phi z St i * ∑ d : Fin (T + 1), I.g z i d * W z d else 0)
      = I.F t z * y t z Sh * (if Sh ∈ I.feas then 1 else 0) * (Df (a z) Sh Sb *
        (if i ∈ Sb then I.phi z Sh i * ∑ d : Fin (T + 1), I.g z i d * W z d else 0)) := by
    intro z Sh Sb
    have e : ∑ St, I.F t z * y t z Sh * (if Sh ∈ I.feas then 1 else 0)
      * Df (a z) Sh Sb * subAssort (I.phi z) Sb (fun i => I.phi z Sh i) St
        * (if i ∈ St then I.phi z St i * ∑ d : Fin (T + 1), I.g z i d * W z d else 0)
        = I.F t z * y t z Sh * (if Sh ∈ I.feas then 1 else 0) * Df (a z) Sh Sb *
          ∑ St, subAssort (I.phi z) Sb (fun i => I.phi z Sh i) St
            * (if i ∈ St then I.phi z St i * ∑ d : Fin (T + 1), I.g z i d * W z d else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun St _ => by ring
    rw [e]
    by_cases hSh : Sh ∈ I.feas
    · by_cases hSb : Sb ⊆ Sh
      · rw [sub_rev I hI z hSh hSb]; ring
      · simp [Df, hSb]
    · simp [hSh]
  simp only [hst]
  have hsb : ∀ z Sh, ∑ Sb, I.F t z * y t z Sh * (if Sh ∈ I.feas then 1 else 0) * (Df (a z) Sh Sb *
        (if i ∈ Sb then I.phi z Sh i * ∑ d : Fin (T + 1), I.g z i d * W z d else 0))
      = I.F t z * y t z Sh * (if Sh ∈ I.feas then 1 else 0) *
        (if i ∈ Sh then a z i * (I.phi z Sh i * ∑ d : Fin (T + 1), I.g z i d * W z d)
          else 0) := by
    intro z Sh
    rw [← Finset.mul_sum, Df_rev]
  simp only [hsb]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.mul_sum]
  rw [← Finset.sum_subset (Finset.subset_univ I.feas)]
  · refine Finset.sum_congr rfl fun S hS => ?_
    rw [if_pos hS]
    split_ifs with hiS
    · ring
    · rw [hI.phi_support z S hS i hiS]; ring
  · intro S _ hS
    rw [if_neg hS]; ring

private lemma Ptr_nonneg {α : Type} [Fintype α] [DecidableEq α] {N : ℕ}
    (K : (Fin N → α) → Fin N → ℝ) (hK0 : ∀ v k, 0 ≤ K v k) (x0 : α) (m : ℕ)
    (v : Fin N → α) : 0 ≤ Ptr K x0 m v := by
  unfold Ptr
  refine Finset.prod_nonneg fun k _ => ?_
  split_ifs
  · exact hK0 v k
  · norm_num
  · norm_num

private lemma Gbar_nonneg (I : Instance n T Z) (hI : I.Assumptions) (z : Z) (i : Fin n)
    (k : ℕ) : 0 ≤ Gbar I z i k :=
  Finset.sum_nonneg fun d _ => hI.g_nonneg z i d

/-- `log (1/(1-γ)) ≥ 2γ/(2-γ)` for `γ ∈ [0,1)`. -/
private lemma log_bound {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ < 1) :
    2 * γ / (2 - γ) ≤ -Real.log (1 - γ) := by
  set w := γ / (2 - γ) with hw
  have h2 : 0 < 2 - γ := by linarith
  have hw0 : 0 ≤ w := div_nonneg h0 h2.le
  have hw1 : w < 1 := by rw [hw, div_lt_one h2]; linarith
  have habs : |w| < 1 := by rw [abs_of_nonneg hw0]; exact hw1
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one habs
  have hle := le_hasSum hs 0 (fun j _ => by positivity)
  have e1 : 1 + w = 2 / (2 - γ) := by rw [hw]; field_simp; ring
  have e2 : 1 - w = 2 * (1 - γ) / (2 - γ) := by rw [hw]; field_simp; ring
  have hlog : Real.log (1 + w) - Real.log (1 - w) = -Real.log (1 - γ) := by
    rw [e1, e2, ← Real.log_div (by positivity) (by
      have : 0 < 1 - γ := by linarith
      positivity)]
    rw [show 2 / (2 - γ) / (2 * (1 - γ) / (2 - γ)) = (1 - γ)⁻¹ by
      field_simp]
    rw [Real.log_inv]
  rw [← hlog]
  simp only [Nat.cast_zero, mul_zero, zero_add, div_one, mul_one, pow_one] at hle
  rw [hw] at hle ⊢
  calc 2 * γ / (2 - γ) = 2 * (γ / (2 - γ)) := by ring
    _ ≤ _ := hle

end Spec2

section VDP

variable {n T : ℕ} {Z : Type} [Fintype Z] [DecidableEq Z]

private lemma V_gt (I : Instance n T Z) (y : ℕ → Z → Finset (Fin n) → ℝ) (i : Fin n)
    {t : ℕ} (h : T < t) : V I y i t = 0 := by
  rw [V, dif_pos h]

private lemma V_le (I : Instance n T Z) (y : ℕ → Z → Finset (Fin n) → ℝ) (i : Fin n)
    {t : ℕ} (h : t ≤ T) : V I y i t =
    ∑ z, ∑ S ∈ I.feas, X I y t z S *
    max (V I y i (t + 1))
      ((1 - I.phi z S i) * V I y i (t + 1)
        + I.phi z S i *
          ((1 / (I.c i : ℝ)) * ∑ d ∈ Finset.Icc 1 T,
              I.g z i d * (I.r z i + V I y i (t + d))
            + (((I.c i : ℝ) - 1) / (I.c i : ℝ)) * V I y i (t + 1))) := by
  rw [V, dif_neg (not_lt.mpr h)]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.sum_attach (Finset.Icc 1 T) (fun d => I.g z i d * (I.r z i + V I y i (t + d)))]

private lemma sum_aux {ι κ : Type} (s : Finset ι) (u : ι → Finset κ)
    (X B P Q : ι → κ → ℝ) (c A : ℝ) (h : ∀ z S, c * B z S = c * A + P z S + Q z S) :
    c * ∑ z ∈ s, ∑ S ∈ u z, X z S * B z S
      = c * A * ∑ z ∈ s, ∑ S ∈ u z, X z S
        + ∑ z ∈ s, ∑ S ∈ u z, X z S * P z S + ∑ z ∈ s, ∑ S ∈ u z, X z S * Q z S := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun S _ => ?_
  rw [show c * (X z S * B z S) = X z S * (c * B z S) by ring, h]
  ring

/-- One step of the optimistic DP: `𝒱_{t+1} ≤ 𝒱_t` and the "Bellman" lower bound
`c (𝒱_t - 𝒱_{t+1}) ≥ Σ X φ r + Σ X φ Σ_d g(d) (𝒱_{t+d} - 𝒱_{t+1})`. -/
private lemma V_step (I : Instance n T Z) (hI : I.Assumptions)
    (y : ℕ → Z → Finset (Fin n) → ℝ) (hy : LPFeasible I y) (hN : Normalized I y)
    (i : Fin n) {t : ℕ} (ht : t ∈ Finset.Icc 1 T) :
    V I y i (t + 1) ≤ V I y i t ∧
    ∑ z, ∑ S ∈ I.feas, X I y t z S * I.phi z S i * I.r z i
      + ∑ z, ∑ S ∈ I.feas, X I y t z S * I.phi z S i *
          ∑ d ∈ Finset.Icc 1 T, I.g z i d * (V I y i (t + d) - V I y i (t + 1))
      ≤ (I.c i : ℝ) * (V I y i t - V I y i (t + 1)) := by
  have htT : t ≤ T := (Finset.mem_Icc.mp ht).2
  set A := V I y i (t + 1) with hA
  have hc : (0 : ℝ) < I.c i := by exact_mod_cast hI.one_le_c i
  have hX0 : ∀ z, ∀ S ∈ I.feas, 0 ≤ X I y t z S := fun z S hS =>
    mul_nonneg (hy.1 t ht z S hS) (hI.F_nonneg t z)
  have hXsum : ∑ z, ∑ S ∈ I.feas, X I y t z S = 1 := by
    unfold X
    simp_rw [← Finset.sum_mul]
    rw [← hI.F_sum t ht]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [hN t ht z, one_mul]
  have hgs := hI.g_sum
  rw [V_le I y i htT]
  constructor
  · calc A = ∑ z, ∑ S ∈ I.feas, X I y t z S * A := by
          simp_rw [← Finset.sum_mul]; rw [hXsum, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun z _ => Finset.sum_le_sum fun S hS =>
          mul_le_mul_of_nonneg_left (le_max_left _ _) (hX0 z S hS)
  · -- the B branch
    have hB : ∀ z S, (I.c i : ℝ) * ((1 - I.phi z S i) * A
        + I.phi z S i *
          ((1 / (I.c i : ℝ)) * ∑ d ∈ Finset.Icc 1 T,
              I.g z i d * (I.r z i + V I y i (t + d))
            + (((I.c i : ℝ) - 1) / (I.c i : ℝ)) * A))
        = (I.c i : ℝ) * A + I.phi z S i * I.r z i
          + I.phi z S i * ∑ d ∈ Finset.Icc 1 T, I.g z i d * (V I y i (t + d) - A) := by
      intro z S
      have e1 : ∑ d ∈ Finset.Icc 1 T, I.g z i d * (I.r z i + V I y i (t + d))
          = I.r z i + ∑ d ∈ Finset.Icc 1 T, I.g z i d * V I y i (t + d) := by
        simp_rw [mul_add, Finset.sum_add_distrib]
        rw [← Finset.sum_mul, hgs z i, one_mul]
      have e2 : ∑ d ∈ Finset.Icc 1 T, I.g z i d * (V I y i (t + d) - A)
          = ∑ d ∈ Finset.Icc 1 T, I.g z i d * V I y i (t + d) - A := by
        simp_rw [mul_sub, Finset.sum_sub_distrib]
        rw [← Finset.sum_mul, hgs z i, one_mul]
      rw [e1, e2]
      field_simp
      ring
    have hge : ∑ z, ∑ S ∈ I.feas, X I y t z S * ((1 - I.phi z S i) * A
        + I.phi z S i *
          ((1 / (I.c i : ℝ)) * ∑ d ∈ Finset.Icc 1 T,
              I.g z i d * (I.r z i + V I y i (t + d))
            + (((I.c i : ℝ) - 1) / (I.c i : ℝ)) * A))
        ≤ ∑ z, ∑ S ∈ I.feas, X I y t z S * max A ((1 - I.phi z S i) * A
        + I.phi z S i *
          ((1 / (I.c i : ℝ)) * ∑ d ∈ Finset.Icc 1 T,
              I.g z i d * (I.r z i + V I y i (t + d))
            + (((I.c i : ℝ) - 1) / (I.c i : ℝ)) * A)) :=
      Finset.sum_le_sum fun z _ => Finset.sum_le_sum fun S hS =>
          mul_le_mul_of_nonneg_left (le_max_right _ _) (hX0 z S hS)
    have hmul := mul_le_mul_of_nonneg_left hge hc.le
    rw [sum_aux Finset.univ (fun _ => I.feas) (fun z S => X I y t z S) _
      (fun z S => I.phi z S i * I.r z i)
      (fun z S => I.phi z S i * ∑ d ∈ Finset.Icc 1 T, I.g z i d * (V I y i (t + d) - A))
      _ A hB, hXsum] at hmul
    simp only [← mul_assoc] at hmul ⊢
    linarith



private lemma V_nonneg (I : Instance n T Z) (hI : I.Assumptions)
    (y : ℕ → Z → Finset (Fin n) → ℝ) (hy : LPFeasible I y) (hN : Normalized I y)
    (i : Fin n) : ∀ s, 1 ≤ s → 0 ≤ V I y i s := by
  have H : ∀ d s, T + 1 - s = d → 1 ≤ s → 0 ≤ V I y i s := by
    intro d
    induction d with
    | zero => intro s hs _; rw [V_gt I y i (by omega)]
    | succ d ih =>
      intro s hs hs1
      have hsT : s ≤ T := by omega
      have := (V_step I hI y hy hN i (Finset.mem_Icc.mpr ⟨hs1, hsT⟩)).1
      have := ih (s + 1) (by omega) (by omega)
      linarith
  exact fun s hs => H _ s rfl hs

end VDP

section Value

variable {α : Type} [Fintype α] [DecidableEq α] {N : ℕ}

/-- Backward value of the per-step rewards `rv` from step `k` on, given the prefix `v`. -/
private noncomputable def Wv (K : (Fin N → α) → Fin N → ℝ) (rv : Fin N → α → ℝ) (k : ℕ)
    (v : Fin N → α) : ℝ :=
  if h : k < N then
    ∑ x, K (Function.update v ⟨k, h⟩ x) ⟨k, h⟩
      * (rv ⟨k, h⟩ x + Wv K rv (k + 1) (Function.update v ⟨k, h⟩ x))
  else 0
termination_by N - k

private lemma Ptr_zero_eval (K : (Fin N → α) → Fin N → ℝ) (x0 : α) (f : (Fin N → α) → ℝ) :
    ∑ v, Ptr K x0 0 v * f v = f (fun _ => x0) := by
  rw [Finset.sum_eq_single (fun _ => x0)]
  · unfold Ptr; simp
  · intro v _ hv
    have : ∃ k, v k ≠ x0 := by
      by_contra h
      push Not at h
      exact hv (funext h)
    obtain ⟨k, hk⟩ := this
    unfold Ptr
    rw [Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk]), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma value_eq (K : (Fin N → α) → Fin N → ℝ) (x0 : α)
    (hK : ∀ k : Fin N, DepLt (fun v => K v k) (k.1 + 1))
    (hK1 : ∀ v (k : Fin N), ∑ x, K (Function.update v k x) k = 1)
    (rv : Fin N → α → ℝ) :
    ∑ v, (∏ k, K v k) * ∑ k, rv k (v k) = Wv K rv 0 (fun _ => x0) := by
  obtain ⟨G, hG⟩ : ∃ G : ℕ → (Fin N → α) → ℝ, ∀ k v,
      G k v = (∑ j : Fin N, if j.1 < k then rv j (v j) else 0) + Wv K rv k v :=
    ⟨fun k v => (∑ j : Fin N, if j.1 < k then rv j (v j) else 0) + Wv K rv k v,
      fun _ _ => rfl⟩
  have hinv : ∀ k (hk : k < N),
      ∑ v, Ptr K x0 (k + 1) v * G (k + 1) v = ∑ v, Ptr K x0 k v * G k v := by
    intro k hk
    rw [step_eq K x0 hK ⟨k, hk⟩]
    refine Finset.sum_congr rfl fun v _ => ?_
    congr 1
    have hS : ∀ x, (∑ j : Fin N, if j.1 < k + 1 then rv j (Function.update v ⟨k, hk⟩ x j) else 0)
        = (∑ j : Fin N, if j.1 < k then rv j (v j) else 0) + rv ⟨k, hk⟩ x := by
      intro x
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (⟨k, hk⟩ : Fin N)),
        ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (⟨k, hk⟩ : Fin N))]
      simp only [Function.update_self, lt_add_iff_pos_right, zero_lt_one, if_true,
        lt_irrefl, if_false, zero_add]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjk : j ≠ ⟨k, hk⟩ := Finset.ne_of_mem_erase hj
      have hjk' : j.1 ≠ k := fun h => hjk (Fin.ext h)
      rw [Function.update_of_ne hjk]
      by_cases hlt : j.1 < k
      · rw [if_pos (by omega), if_pos hlt]
      · rw [if_neg (by omega), if_neg hlt]
    simp only [hG, hS]
    rw [Wv, dif_pos hk]
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hK1, one_mul]
    rw [← add_assoc]
  have hall : ∀ k, k ≤ N → ∑ v, Ptr K x0 k v * G k v = ∑ v, Ptr K x0 0 v * G 0 v := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih => intro hk; rw [hinv k (by omega)]; exact ih (by omega)
  have hN' := hall N le_rfl
  rw [Ptr_zero_eval] at hN'
  have hfull : ∀ v, Ptr K x0 N v = ∏ k, K v k := by
    intro v; unfold Ptr
    exact Finset.prod_congr rfl fun k _ => by rw [if_pos k.2]
  have hGN : ∀ v, G N v = ∑ k, rv k (v k) := by
    intro v
    rw [hG, Wv, dif_neg (lt_irrefl N), add_zero]
    exact Finset.sum_congr rfl fun j _ => by rw [if_pos j.2]
  simp only [hfull, hGN] at hN'
  rw [hN', hG]
  simp

end Value

theorem solution {n T : ℕ} {Z : Type} [Fintype Z] [DecidableEq Z]
    (I : Instance n T Z) (hI : I.Assumptions)
    (y : ℕ → Z → Finset (Fin n) → ℝ) (hy : LPFeasible I y) (hN : Normalized I y)
    (t : ℕ) (ht : t ∈ Finset.Icc 1 T)
    (ret : Fin n → ℕ → ℕ) (hret : ValidStart I t ret)
    (rule : Fin n → Rule Z) (hrule : ∀ j, (rule j).Valid)
    (i : Fin n) (hi : rule i = Rule.threshold (P I y i)) :
    ((I.c i - ∑ s ∈ Finset.Ioc t (t + T), ret i s : ℕ) : ℝ) * V I y i t
      ≤ expRevProd I y rule t ret i := by
  classical
  have ht1 := (Finset.mem_Icc.mp ht).1
  have htT := (Finset.mem_Icc.mp ht).2
  have hZ : Nonempty Z := by
    by_contra hZ
    rw [not_nonempty_iff] at hZ
    have := hI.F_sum t ht
    simp at this
  obtain ⟨z0⟩ := hZ
  let x0 : Step n T Z := (z0, ∅, ∅, ∅, none, 0)
  set N := T + 1 - t with hNdef
  set K := kernel I y rule t ret with hKdef
  have hK : ∀ k : Fin N, DepLt (fun v => K v k) (k.1 + 1) :=
    fun k => kernel_dep I y rule t ret k
  have hK1 : ∀ v (k : Fin N), ∑ x, K (Function.update v k x) k = 1 := by
    intro v k
    simp only [hKdef, kernel_update]
    exact kstep_sum I hI y hN (Finset.mem_Icc.mpr ⟨by omega, by have := k.2; omega⟩) _
  have hK0 : ∀ v k, 0 ≤ K v k := fun v k =>
    kernel_nonneg I hI y hy rule hrule t ht1 ret v k
  set c : ℝ := (I.c i : ℝ) with hc
  have hcpos : 0 < c := by rw [hc]; exact_mod_cast hI.one_le_c i
  have hV0 := V_nonneg I hI y hy hN i
  -- the per-step revenue
  obtain ⟨rv, hrv⟩ : ∃ rv : Fin N → Step n T Z → ℝ, ∀ k x,
      rv k x = if x.2.2.2.2.1 = some i then I.r x.1 i else 0 :=
    ⟨fun _ x => if x.2.2.2.2.1 = some i then I.r x.1 i else 0, fun _ _ => rfl⟩
  -- the potential
  obtain ⟨Acnt, hAcnt⟩ : ∃ A : ℕ → ℕ, ∀ k, A k = ∑ s ∈ Finset.Ioc (t + k) (t + T), ret i s :=
    ⟨fun k => ∑ s ∈ Finset.Ioc (t + k) (t + T), ret i s, fun _ => rfl⟩
  obtain ⟨cnd, hcnd⟩ : ∃ cnd : ℕ → (Fin N → Step n T Z) → Fin N → Prop, ∀ k v j,
      cnd k v j = (j.1 < k ∧ (v j).2.2.2.2.1 = some i ∧ k < j.1 + ((v j).2.2.2.2.2 : ℕ)) :=
    ⟨fun k v j => j.1 < k ∧ (v j).2.2.2.2.1 = some i ∧ k < j.1 + ((v j).2.2.2.2.2 : ℕ),
      fun _ _ _ => rfl⟩
  obtain ⟨Phi, hPhi⟩ : ∃ Phi : ℕ → (Fin N → Step n T Z) → ℝ, ∀ k v,
      Phi k v = ((c - (Acnt k : ℝ) - ∑ j : Fin N, if cnd k v j then (1 : ℝ) else 0)
          * V I y i (t + k))
        + ((∑ s ∈ Finset.Ioc (t + k) (t + T), (ret i s : ℝ) * V I y i s)
          + ∑ j : Fin N, if cnd k v j then V I y i (t + j.1 + ((v j).2.2.2.2.2 : ℕ)) else 0) :=
    ⟨_, fun _ _ => rfl⟩
  -- the potential at the start
  have hstart : ∀ v, ((I.c i - ∑ s ∈ Finset.Ioc t (t + T), ret i s : ℕ) : ℝ) * V I y i t
      ≤ Phi 0 v := by
    intro v
    rw [hPhi]
    have hc0 : ∀ j : Fin N, ¬ cnd 0 v j := fun j h => by rw [hcnd] at h; omega
    simp only [hc0, if_false, Finset.sum_const_zero, sub_zero, add_zero]
    rw [hAcnt, Nat.cast_sub (by simpa using hret.2 i), add_zero]
    have : 0 ≤ ∑ s ∈ Finset.Ioc t (t + T), (ret i s : ℝ) * V I y i s :=
      Finset.sum_nonneg fun s hs => mul_nonneg (Nat.cast_nonneg _)
        (hV0 s (by simp only [Finset.mem_Ioc] at hs; omega))
    rw [hc]; push_cast; linarith
  -- the potential vanishes at the horizon
  have hend : ∀ v, Phi N v = 0 := by
    intro v
    rw [hPhi]
    have h1 : V I y i (t + N) = 0 := V_gt I y i (by omega)
    have h2 : ∀ s ∈ Finset.Ioc (t + N) (t + T), (ret i s : ℝ) * V I y i s = 0 := by
      intro s hs; simp only [Finset.mem_Ioc] at hs; rw [V_gt I y i (by omega), mul_zero]
    have h3 : ∀ j : Fin N, (if cnd N v j then V I y i (t + j.1 + ((v j).2.2.2.2.2 : ℕ)) else 0)
        = 0 := by
      intro j
      split_ifs with h
      · rw [hcnd] at h; exact V_gt I y i (by omega)
      · rfl
    rw [h1, Finset.sum_eq_zero h2, Finset.sum_eq_zero (fun j _ => h3 j)]
    ring
  -- the update identity
  have hupd : ∀ (k : ℕ) (hk : k < N) v x, Phi (k + 1) (Function.update v ⟨k, hk⟩ x)
      = Phi k v + ((c - (Acnt k : ℝ) - ∑ j : Fin N, if cnd k v j then (1 : ℝ) else 0)
          * (V I y i (t + (k + 1)) - V I y i (t + k)))
        + (if x.2.2.2.2.1 = some i ∧ 1 < (x.2.2.2.2.2 : ℕ)
            then V I y i (t + k + (x.2.2.2.2.2 : ℕ)) - V I y i (t + k + 1) else 0) := by
    intro k hk v x
    set w := Function.update v ⟨k, hk⟩ x with hw
    set V' := V I y i (t + k + 1) with hV'
    have hA : (Acnt k : ℝ) = Acnt (k + 1) + ret i (t + k + 1) := by
      rw [hAcnt, hAcnt]
      have : Finset.Ioc (t + k) (t + T) = insert (t + k + 1) (Finset.Ioc (t + (k + 1)) (t + T)) := by
        ext s; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
      rw [this, Finset.sum_insert (by simp)]
      push_cast; ring
    have hRs : ∑ s ∈ Finset.Ioc (t + k) (t + T), (ret i s : ℝ) * V I y i s
        = ∑ s ∈ Finset.Ioc (t + (k + 1)) (t + T), (ret i s : ℝ) * V I y i s
          + (ret i (t + k + 1) : ℝ) * V' := by
      have : Finset.Ioc (t + k) (t + T) = insert (t + k + 1) (Finset.Ioc (t + (k + 1)) (t + T)) := by
        ext s; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
      rw [this, Finset.sum_insert (by simp)]
      ring
    -- per-`j` comparison
    have hj : ∀ j : Fin N,
        (if cnd (k + 1) w j then V I y i (t + j.1 + ((w j).2.2.2.2.2 : ℕ)) else 0)
          - (if cnd (k + 1) w j then (1 : ℝ) else 0) * V'
        = (if cnd k v j then V I y i (t + j.1 + ((v j).2.2.2.2.2 : ℕ)) else 0)
          - (if cnd k v j then (1 : ℝ) else 0) * V'
          + (if j = ⟨k, hk⟩ then (if x.2.2.2.2.1 = some i ∧ 1 < (x.2.2.2.2.2 : ℕ)
            then V I y i (t + k + (x.2.2.2.2.2 : ℕ)) - V' else 0) else 0) := by
      intro j
      by_cases hjk : j = ⟨k, hk⟩
      · subst hjk
        have hwk : w ⟨k, hk⟩ = x := by rw [hw, Function.update_self]
        have hn : ¬ cnd k v ⟨k, hk⟩ := by rw [hcnd]; simp
        simp only [hn, if_false, if_true, zero_mul, sub_zero, zero_add]
        rw [hcnd, hwk]
        by_cases hx : x.2.2.2.2.1 = some i ∧ 1 < (x.2.2.2.2.2 : ℕ)
        · rw [if_pos ⟨by simp, hx.1, by simp only [Fin.val_mk]; omega⟩, if_pos hx,
            if_pos ⟨by simp, hx.1, by simp only [Fin.val_mk]; omega⟩]
          ring
        · rw [if_neg (fun h => hx ⟨h.2.1, by have := h.2.2; simp at this; omega⟩), if_neg hx,
            if_neg (fun h => hx ⟨h.2.1, by have := h.2.2; simp at this; omega⟩)]
          ring
      · have hwj : w j = v j := by rw [hw, Function.update_of_ne hjk]
        have hjk' : j.1 ≠ k := fun h => hjk (Fin.ext h)
        rw [if_neg hjk, add_zero]
        rw [hcnd, hcnd, hwj]
        by_cases hlt : j.1 < k
        · by_cases hch : (v j).2.2.2.2.1 = some i
          · by_cases h1 : k + 1 < j.1 + ((v j).2.2.2.2.2 : ℕ)
            · rw [if_pos ⟨by omega, hch, h1⟩, if_pos ⟨by omega, hch, h1⟩,
                if_pos ⟨hlt, hch, by omega⟩, if_pos ⟨hlt, hch, by omega⟩]
            · rw [if_neg (fun h => h1 h.2.2), if_neg (fun h => h1 h.2.2)]
              by_cases h2 : k < j.1 + ((v j).2.2.2.2.2 : ℕ)
              · rw [if_pos ⟨hlt, hch, h2⟩, if_pos ⟨hlt, hch, h2⟩]
                have : t + j.1 + ((v j).2.2.2.2.2 : ℕ) = t + k + 1 := by omega
                rw [this, hV']; ring
              · rw [if_neg (fun h => h2 h.2.2), if_neg (fun h => h2 h.2.2)]
          · rw [if_neg (fun h => hch h.2.1), if_neg (fun h => hch h.2.1),
              if_neg (fun h => hch h.2.1), if_neg (fun h => hch h.2.1)]
        · rw [if_neg (fun h => by omega), if_neg (fun h => by omega),
            if_neg (fun h => hlt h.1), if_neg (fun h => hlt h.1)]
    have hsum := Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hj j)
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_ite_eq' Finset.univ, if_pos (Finset.mem_univ _)] at hsum
    rw [← Finset.sum_mul, ← Finset.sum_mul] at hsum
    rw [hPhi, hPhi, hA, hRs]
    have e1 : t + (k + 1) = t + k + 1 := by ring
    rw [e1, ← hV']
    linear_combination hsum
  -- the Bellman identity: `c (𝒱_τ - 𝒱_{τ+1}) = Σ F y φ (r - P)⁺`
  have hVD : ∀ τ ∈ Finset.Icc 1 T, c * (V I y i τ - V I y i (τ + 1))
      = ∑ z, ∑ S ∈ I.feas, I.F τ z * y τ z S * I.phi z S i
          * max 0 (I.r z i - P I y i τ z) := by
    intro τ hτ
    have hτT : τ ≤ T := (Finset.mem_Icc.mp hτ).2
    have hXsum : ∑ z, ∑ S ∈ I.feas, X I y τ z S = 1 := by
      unfold X
      simp_rw [← Finset.sum_mul]
      rw [← hI.F_sum τ hτ]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [hN τ hτ z, one_mul]
    rw [V_le I y i hτT]
    have hmax : ∀ z, ∀ S ∈ I.feas, X I y τ z S * max (V I y i (τ + 1))
        ((1 - I.phi z S i) * V I y i (τ + 1)
          + I.phi z S i *
            ((1 / (I.c i : ℝ)) * ∑ d ∈ Finset.Icc 1 T,
                I.g z i d * (I.r z i + V I y i (τ + d))
              + (((I.c i : ℝ) - 1) / (I.c i : ℝ)) * V I y i (τ + 1)))
        = X I y τ z S * V I y i (τ + 1)
          + (1 / c) * (I.F τ z * y τ z S * I.phi z S i * max 0 (I.r z i - P I y i τ z)) := by
      intro z S hz
      have hsum1 : ∑ d ∈ Finset.Icc 1 T, I.g z i d * (I.r z i + V I y i (τ + d))
          = I.r z i + ∑ d ∈ Finset.Icc 1 T, I.g z i d * V I y i (τ + d) := by
        simp_rw [mul_add, Finset.sum_add_distrib]
        rw [← Finset.sum_mul, hI.g_sum z i, one_mul]
      have hB : (1 - I.phi z S i) * V I y i (τ + 1)
          + I.phi z S i *
            ((1 / (I.c i : ℝ)) * ∑ d ∈ Finset.Icc 1 T,
                I.g z i d * (I.r z i + V I y i (τ + d))
              + (((I.c i : ℝ) - 1) / (I.c i : ℝ)) * V I y i (τ + 1))
          = V I y i (τ + 1) + (I.phi z S i / c) * (I.r z i - P I y i τ z) := by
        rw [hsum1, P, ← hc]
        field_simp
        ring
      rw [hB]
      have hφc : 0 ≤ I.phi z S i / c := div_nonneg (hI.phi_nonneg z S hz i) hcpos.le
      have : max (V I y i (τ + 1)) (V I y i (τ + 1) + I.phi z S i / c * (I.r z i - P I y i τ z))
          = V I y i (τ + 1) + I.phi z S i / c * max 0 (I.r z i - P I y i τ z) := by
        rcases le_total 0 (I.r z i - P I y i τ z) with h | h
        · rw [max_eq_right h, max_eq_right (by nlinarith)]
        · rw [max_eq_left h, max_eq_left (by nlinarith)]; ring
      rw [this]
      unfold X
      field_simp
    have e : ∑ z, ∑ S ∈ I.feas, X I y τ z S * max (V I y i (τ + 1))
        ((1 - I.phi z S i) * V I y i (τ + 1)
          + I.phi z S i *
            ((1 / (I.c i : ℝ)) * ∑ d ∈ Finset.Icc 1 T,
                I.g z i d * (I.r z i + V I y i (τ + d))
              + (((I.c i : ℝ) - 1) / (I.c i : ℝ)) * V I y i (τ + 1)))
        = V I y i (τ + 1) * ∑ z, ∑ S ∈ I.feas, X I y τ z S
          + (1 / c) * ∑ z, ∑ S ∈ I.feas, I.F τ z * y τ z S * I.phi z S i
              * max 0 (I.r z i - P I y i τ z) := by
      rw [Finset.sum_congr rfl (fun z _ => Finset.sum_congr rfl (fun S hS => hmax z S hS))]
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun S _ => by ring
    rw [e, hXsum]
    field_simp
    ring
  -- one step of the threshold policy
  have hgain : ∀ (k : ℕ) (hk : k < N) v, ∑ x, K (Function.update v ⟨k, hk⟩ x) ⟨k, hk⟩
      * (rv ⟨k, hk⟩ x + (if x.2.2.2.2.1 = some i ∧ 1 < (x.2.2.2.2.2 : ℕ)
            then V I y i (t + k + (x.2.2.2.2.2 : ℕ)) - V I y i (t + k + 1) else 0))
      = (if onHand I t ret v i k = 0 then 0 else 1) *
        ∑ z, ∑ S ∈ I.feas, I.F (t + k) z * y (t + k) z S * I.phi z S i
          * max 0 (I.r z i - P I y i (t + k) z) := by
    intro k hk v
    have hw := kstep_wrev I hI y (t := t + k) (aOf I rule t ret v k) i
      (fun z d => I.r z i + if 1 < d then V I y i (t + k + d) - V I y i (t + k + 1) else 0)
    have e1 : ∑ x, K (Function.update v ⟨k, hk⟩ x) ⟨k, hk⟩
        * (rv ⟨k, hk⟩ x + (if x.2.2.2.2.1 = some i ∧ 1 < (x.2.2.2.2.2 : ℕ)
            then V I y i (t + k + (x.2.2.2.2.2 : ℕ)) - V I y i (t + k + 1) else 0))
        = ∑ x, kstep I y (t + k) (aOf I rule t ret v k) x
          * (if x.2.2.2.2.1 = some i then I.r x.1 i + (if 1 < (x.2.2.2.2.2 : ℕ)
            then V I y i (t + k + (x.2.2.2.2.2 : ℕ)) - V I y i (t + k + 1) else 0) else 0) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hKdef, kernel_update, hrv]
      congr 1
      by_cases h1 : x.2.2.2.2.1 = some i
      · by_cases h2 : 1 < (x.2.2.2.2.2 : ℕ)
        · rw [if_pos h1, if_pos ⟨h1, h2⟩, if_pos h1, if_pos h2]
        · rw [if_pos h1, if_neg (fun h => h2 h.2), if_pos h1, if_neg h2]
      · rw [if_neg h1, if_neg (fun h => h1 h.1), if_neg h1]; ring
    rw [e1, hw]
    have hd : ∀ z, ∑ d : Fin (T + 1), I.g z i d * (I.r z i
        + if 1 < (d : ℕ) then V I y i (t + k + d) - V I y i (t + k + 1) else 0)
        = I.r z i - P I y i (t + k) z := by
      intro z
      rw [Fin.sum_univ_eq_sum_range (fun d => I.g z i d * (I.r z i
        + if 1 < d then V I y i (t + k + d) - V I y i (t + k + 1) else 0))]
      have hsub : ∑ d ∈ Finset.range (T + 1), I.g z i d * (I.r z i
          + if 1 < d then V I y i (t + k + d) - V I y i (t + k + 1) else 0)
          = ∑ d ∈ Finset.Icc 1 T, I.g z i d * (I.r z i
          + (V I y i (t + k + d) - V I y i (t + k + 1))) := by
        symm
        apply Finset.sum_subset_zero_on_sdiff
        · intro d hd; simp only [Finset.mem_Icc] at hd; simp only [Finset.mem_range]; omega
        · intro d hd
          simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_Icc] at hd
          have : d = 0 := by omega
          subst this; rw [hI.g_zero]; ring
        · intro d hd
          simp only [Finset.mem_Icc] at hd
          by_cases h : 1 < d
          · rw [if_pos h]
          · have : d = 1 := by omega
            subst this; simp
      rw [hsub, P]
      simp_rw [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [← Finset.sum_mul, ← Finset.sum_mul, hI.g_sum z i, one_mul, one_mul]
      ring_nf
    simp only [hd]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    simp only [aOf, hi, keep]
    split_ifs with h0 hP
    · ring
    · rw [max_eq_right (by linarith)]; ring
    · rw [max_eq_left (by linarith)]; ring
  -- backward induction
  have hlow : ∀ r k, k + r = N → ∀ v, Phi k v ≤ Wv K rv k v := by
    intro r
    induction r with
    | zero =>
      intro k hk v
      have hkN : k = N := by omega
      subst hkN
      rw [hend]
      unfold Wv
      split_ifs with h
      · exact absurd h (lt_irrefl _)
      · exact le_refl _
    | succ r ih =>
      intro k hkr v
      have hk : k < N := by omega
      rw [Wv, dif_pos hk]
      have hτ : t + k ∈ Finset.Icc 1 T := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      set u := c - (Acnt k : ℝ) - ∑ j : Fin N, if cnd k v j then (1 : ℝ) else 0 with hu
      have hstep : ∀ x, K (Function.update v ⟨k, hk⟩ x) ⟨k, hk⟩
          * (rv ⟨k, hk⟩ x + (Phi k v + u * (V I y i (t + (k + 1)) - V I y i (t + k))
            + (if x.2.2.2.2.1 = some i ∧ 1 < (x.2.2.2.2.2 : ℕ)
              then V I y i (t + k + (x.2.2.2.2.2 : ℕ)) - V I y i (t + k + 1) else 0)))
          ≤ K (Function.update v ⟨k, hk⟩ x) ⟨k, hk⟩
            * (rv ⟨k, hk⟩ x + Wv K rv (k + 1) (Function.update v ⟨k, hk⟩ x)) := by
        intro x
        refine mul_le_mul_of_nonneg_left ?_ (hK0 _ _)
        have := ih (k + 1) (by omega) (Function.update v ⟨k, hk⟩ x)
        rw [hupd k hk v x] at this
        linarith
      refine le_trans ?_ (Finset.sum_le_sum fun x _ => hstep x)
      have hsplit : ∑ x, K (Function.update v ⟨k, hk⟩ x) ⟨k, hk⟩
          * (rv ⟨k, hk⟩ x + (Phi k v + u * (V I y i (t + (k + 1)) - V I y i (t + k))
            + (if x.2.2.2.2.1 = some i ∧ 1 < (x.2.2.2.2.2 : ℕ)
              then V I y i (t + k + (x.2.2.2.2.2 : ℕ)) - V I y i (t + k + 1) else 0)))
          = (Phi k v + u * (V I y i (t + (k + 1)) - V I y i (t + k)))
            + ∑ x, K (Function.update v ⟨k, hk⟩ x) ⟨k, hk⟩
              * (rv ⟨k, hk⟩ x + (if x.2.2.2.2.1 = some i ∧ 1 < (x.2.2.2.2.2 : ℕ)
                then V I y i (t + k + (x.2.2.2.2.2 : ℕ)) - V I y i (t + k + 1) else 0)) := by
        have : ∀ x, K (Function.update v ⟨k, hk⟩ x) ⟨k, hk⟩
            * (rv ⟨k, hk⟩ x + (Phi k v + u * (V I y i (t + (k + 1)) - V I y i (t + k))
              + (if x.2.2.2.2.1 = some i ∧ 1 < (x.2.2.2.2.2 : ℕ)
                then V I y i (t + k + (x.2.2.2.2.2 : ℕ)) - V I y i (t + k + 1) else 0)))
            = (Phi k v + u * (V I y i (t + (k + 1)) - V I y i (t + k)))
              * K (Function.update v ⟨k, hk⟩ x) ⟨k, hk⟩
              + K (Function.update v ⟨k, hk⟩ x) ⟨k, hk⟩
                * (rv ⟨k, hk⟩ x + (if x.2.2.2.2.1 = some i ∧ 1 < (x.2.2.2.2.2 : ℕ)
                  then V I y i (t + k + (x.2.2.2.2.2 : ℕ)) - V I y i (t + k + 1) else 0)) := by
          intro x; ring
        simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hK1, mul_one]
      rw [hsplit, hgain k hk v]
      -- remaining inequality
      set D := ∑ z, ∑ S ∈ I.feas, I.F (t + k) z * y (t + k) z S * I.phi z S i
          * max 0 (I.r z i - P I y i (t + k) z) with hD
      have hD0 : 0 ≤ D := by
        refine Finset.sum_nonneg fun z _ => Finset.sum_nonneg fun S hS => ?_
        have := hy.1 (t + k) hτ z S hS
        have := hI.F_nonneg (t + k) z
        have := hI.phi_nonneg z S hS i
        have : 0 ≤ max 0 (I.r z i - P I y i (t + k) z) := le_max_left _ _
        positivity
      have hVk := hVD (t + k) hτ
      rw [← hD] at hVk
      have e2 : t + (k + 1) = t + k + 1 := by ring
      rw [e2]
      have hu_le : u ≤ c := by
        have : 0 ≤ ∑ j : Fin N, if cnd k v j then (1 : ℝ) else 0 :=
          Finset.sum_nonneg fun j _ => by split_ifs <;> norm_num
        have : (0 : ℝ) ≤ Acnt k := Nat.cast_nonneg _
        rw [hu]; linarith
      -- `c (𝒱_{t+k+1} - 𝒱_{t+k}) = -D`
      have hdiff : V I y i (t + k + 1) - V I y i (t + k) = -(D / c) := by
        field_simp; linarith
      rw [hdiff]
      split_ifs with h0
      · -- no unit on hand: `u ≤ 0`
        have hle : (I.c i : ℝ) ≤ Acnt k + ∑ j : Fin N, if cnd k v j then (1 : ℝ) else 0 := by
          simp only [onHand] at h0
          rw [Nat.sub_sub] at h0
          have h0n := Nat.sub_eq_zero_iff_le.mp h0
          have h0R := (Nat.cast_le (α := ℝ)).mpr h0n
          rw [Nat.cast_add, Finset.natCast_card_filter] at h0R
          rw [hAcnt]
          refine h0R.trans (le_of_eq ?_)
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hcnd]
          split_ifs <;> rfl
        have hu0 : u ≤ 0 := by rw [hu, hc]; linarith
        have : 0 ≤ u * -(D / c) := by
          have : 0 ≤ D / c := div_nonneg hD0 hcpos.le
          nlinarith
        linarith
      · have : u * (D / c) ≤ D := by
          rw [mul_div_assoc']
          rw [div_le_iff₀ hcpos]
          nlinarith
        linarith
  -- conclusion
  have hval := value_eq K x0 hK hK1 rv
  have hexp : expRevProd I y rule t ret i = ∑ v, (∏ k, K v k) * ∑ k, rv k (v k) := by
    unfold expRevProd pathProb
    refine Finset.sum_congr rfl fun v _ => ?_
    congr 1
    rw [← Fin.sum_univ_eq_sum_range (fun k => revAt I t i k v) N]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [revAt, dif_pos k.2, hrv]
  rw [hexp, hval]
  exact (hstart _).trans (hlow N 0 (by omega) _)
