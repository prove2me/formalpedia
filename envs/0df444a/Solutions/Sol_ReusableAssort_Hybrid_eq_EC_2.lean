-- Prove2me | solution 1 for ReusableAssort.Hybrid.eq_EC_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T06:45:27.295751+00:00
-- url     : https://prove2.me/submissions/e7a585cd-d340-43ab-9dd8-560de0f2dacb

import Mathlib
import Definitions.Def_ReusableAssort_Hybrid_Process
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

theorem solution {n T : ℕ} {Z : Type} [Fintype Z] [DecidableEq Z]
    (I : Instance n T Z) (hI : I.Assumptions)
    (y : ℕ → Z → Finset (Fin n) → ℝ) (hy : LPFeasible I y) (hN : Normalized I y)
    (rule : Fin n → Rule Z) (hrule : ∀ j, (rule j).Valid)
    (i : Fin n) (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (hi : rule i = Rule.random γ) :
    ∀ t ∈ Finset.Icc 1 T,
      probNoUnit I y rule 1 (fun _ _ => 0) i t
        ≤ Real.exp (-(γ ^ 2 * (I.c i : ℝ) / (2 - γ))) := by
  classical
  intro t ht
  have ht1 := (Finset.mem_Icc.mp ht).1
  have htT := (Finset.mem_Icc.mp ht).2
  have hZ : Nonempty Z := by
    by_contra hZ
    rw [not_nonempty_iff] at hZ
    have := hI.F_sum t ht
    simp at this
  obtain ⟨z0⟩ := hZ
  let x0 : Step n T Z := (z0, ∅, ∅, ∅, none, 0)
  set ret : Fin n → ℕ → ℕ := fun _ _ => 0 with hret
  set K := kernel I y rule 1 ret with hKdef
  have hK : ∀ k : Fin (T + 1 - 1), DepLt (fun v => K v k) (k.1 + 1) :=
    fun k => kernel_dep I y rule 1 ret k
  have hK1 : ∀ v (k : Fin (T + 1 - 1)), ∑ x, K (Function.update v k x) k = 1 := by
    intro v k
    simp only [hKdef, kernel_update]
    exact kstep_sum I hI y hN (Finset.mem_Icc.mpr ⟨by omega, by have := k.2; omega⟩) _
  have hK0 : ∀ v k, 0 ≤ K v k := fun v k =>
    kernel_nonneg I hI y hy rule hrule 1 le_rfl ret v k
  set m := t - 1 with hm
  have hmN : m < T + 1 - 1 := by omega
  set c : ℝ := (I.c i : ℝ) with hc
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  have hg1 : 0 ≤ 1 - γ := by linarith [hγ.2]
  -- choice of the exponential tilt
  obtain ⟨L, hL0, hLb⟩ : ∃ L : ℝ, 0 ≤ L ∧
      -L * c + (Real.exp L - 1) * (1 - γ) * c ≤ -(γ ^ 2 * c / (2 - γ)) := by
    rcases eq_or_lt_of_le hγ.2 with h1 | h1
    · refine ⟨1, zero_le_one, ?_⟩
      rw [h1]; norm_num
    · refine ⟨-Real.log (1 - γ), ?_, ?_⟩
      · have : Real.log (1 - γ) ≤ 0 := Real.log_nonpos (by linarith) (by linarith [hγ.1])
        linarith
      · have hpos : 0 < 1 - γ := by linarith
        have hexp : Real.exp (-Real.log (1 - γ)) = (1 - γ)⁻¹ := by
          rw [Real.exp_neg, Real.exp_log hpos]
        rw [hexp]
        have hlb := log_bound hγ.1 h1
        have h2 : 0 < 2 - γ := by linarith
        have e : ((1 - γ)⁻¹ - 1) * (1 - γ) = γ := by
          rw [sub_mul, inv_mul_cancel₀ hpos.ne', one_mul]; ring
        rw [e]
        have hm1 : -(-Real.log (1 - γ)) * c ≤ -(2 * γ / (2 - γ)) * c :=
          mul_le_mul_of_nonneg_right (by linarith) hc0
        have key : -(2 * γ / (2 - γ)) * c + γ * c = -(γ ^ 2 * c / (2 - γ)) := by
          field_simp; ring
        linarith
  have heL : 0 ≤ Real.exp L - 1 := by linarith [Real.add_one_le_exp L]
  -- indicators of "a unit of `i` rented at step `j` is still out at step `m`"
  obtain ⟨Y, hY⟩ : ∃ Y : ℕ → Step n T Z → ℝ, ∀ j x,
      Y j x = if x.2.2.2.2.1 = some i ∧ m < j + (x.2.2.2.2.2 : ℕ) then 1 else 0 :=
    ⟨fun j x => if x.2.2.2.2.1 = some i ∧ m < j + (x.2.2.2.2.2 : ℕ) then 1 else 0,
      fun _ _ => rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : ℕ → (Fin (T + 1 - 1) → Step n T Z) → ℝ, ∀ k v,
      H k v = ∏ j : Fin (T + 1 - 1), if j.1 < k then Real.exp (L * Y j.1 (v j)) else 1 :=
    ⟨fun k v => ∏ j : Fin (T + 1 - 1), if j.1 < k then Real.exp (L * Y j.1 (v j)) else 1,
      fun _ _ => rfl⟩
  have hH0 : ∀ k v, 0 ≤ H k v := fun k v => by
    rw [hH]; exact Finset.prod_nonneg fun j _ => by split_ifs <;> positivity
  obtain ⟨B, hB⟩ : ∃ B : ℕ → ℝ, ∀ k, B k = ∑ z, ∑ S ∈ I.feas,
      I.F (1 + k) z * Gbar I z i (m - k) * I.phi z S i * y (1 + k) z S :=
    ⟨fun k => ∑ z, ∑ S ∈ I.feas,
      I.F (1 + k) z * Gbar I z i (m - k) * I.phi z S i * y (1 + k) z S, fun _ => rfl⟩
  have hB0 : ∀ k, k < m → 0 ≤ B k := by
    intro k hk
    rw [hB]
    refine Finset.sum_nonneg fun z _ => Finset.sum_nonneg fun S hS => ?_
    have := hy.1 (1 + k) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) z S hS
    have := hI.F_nonneg (1 + k) z
    have := hI.phi_nonneg z S hS i
    have := Gbar_nonneg I hI z i (m - k)
    positivity
  -- one step of the exponential moment
  have hGb : ∀ z k, k < m → ∑ d : Fin (T + 1), I.g z i d *
      (if m < k + (d : ℕ) then (1 : ℝ) else 0) = Gbar I z i (m - k) := by
    intro z k hk
    rw [Fin.sum_univ_eq_sum_range (fun d => I.g z i d * (if m < k + d then (1 : ℝ) else 0))]
    unfold Gbar
    rw [Finset.sum_filter]
    symm
    apply Finset.sum_subset_zero_on_sdiff
    · intro d hd; simp only [Finset.mem_Icc] at hd; simp only [Finset.mem_range]; omega
    · intro d hd
      simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_Icc] at hd
      have : d = 0 := by omega
      subst this; rw [hI.g_zero]; ring
    · intro d hd
      simp only [Finset.mem_Icc] at hd
      by_cases h : m - k < d
      · rw [if_pos h, if_pos (by omega), mul_one]
      · rw [if_neg h, if_neg (by omega), mul_zero]
  have hstep1 : ∀ v (k : ℕ) (hk : k < m), ∑ x, K (Function.update v ⟨k, by omega⟩ x) ⟨k, by omega⟩
      * Real.exp (L * Y k x) ≤ 1 + (Real.exp L - 1) * ((1 - γ) * B k) := by
    intro v k hk
    have hexpY : ∀ x, Real.exp (L * Y k x) = 1 + (Real.exp L - 1) * Y k x := by
      intro x; rw [hY]; split_ifs <;> simp
    simp only [hexpY, mul_add, mul_one, Finset.sum_add_distrib, hK1]
    have hw := kstep_wrev I hI y (t := 1 + k) (aOf I rule 1 ret v k) i
      (fun _ d => if m < k + d then (1 : ℝ) else 0)
    have hq : ∑ x, K (Function.update v ⟨k, by omega⟩ x) ⟨k, by omega⟩
        * ((Real.exp L - 1) * Y k x)
        = (Real.exp L - 1) * ∑ z, aOf I rule 1 ret v k z i *
          ∑ S ∈ I.feas, I.F (1 + k) z * Gbar I z i (m - k) * I.phi z S i * y (1 + k) z S := by
      have e1 : ∑ x, K (Function.update v ⟨k, by omega⟩ x) ⟨k, by omega⟩
          * ((Real.exp L - 1) * Y k x)
          = (Real.exp L - 1) * ∑ x, kstep I y (1 + k) (aOf I rule 1 ret v k) x
            * (if x.2.2.2.2.1 = some i then (if m < k + (x.2.2.2.2.2 : ℕ) then (1 : ℝ) else 0)
              else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [hKdef, kernel_update, hY, ite_and]
        ring
      rw [e1, hw]
      congr 1
      refine Finset.sum_congr rfl fun z _ => ?_
      congr 1
      refine Finset.sum_congr rfl fun S _ => ?_
      rw [hGb z k hk]
    have : ∑ z, aOf I rule 1 ret v k z i *
        ∑ S ∈ I.feas, I.F (1 + k) z * Gbar I z i (m - k) * I.phi z S i * y (1 + k) z S
        ≤ (1 - γ) * B k := by
      rw [hB k, Finset.mul_sum]
      refine Finset.sum_le_sum fun z _ => ?_
      have hin : 0 ≤ ∑ S ∈ I.feas, I.F (1 + k) z * Gbar I z i (m - k) * I.phi z S i
          * y (1 + k) z S := by
        refine Finset.sum_nonneg fun S hS => ?_
        have := hy.1 (1 + k) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) z S hS
        have := hI.F_nonneg (1 + k) z
        have := hI.phi_nonneg z S hS i
        have := Gbar_nonneg I hI z i (m - k)
        positivity
      refine mul_le_mul_of_nonneg_right ?_ hin
      simp only [aOf, hi, keep]
      split_ifs
      · exact hg1
      · exact le_refl _
    nlinarith
  -- induction over the steps
  have hind : ∀ k, k ≤ m → ∑ v, Ptr K x0 k v * H k v
      ≤ ∏ j ∈ Finset.range k, (1 + (Real.exp L - 1) * ((1 - γ) * B j)) := by
    intro k
    induction k with
    | zero =>
      intro _
      have : ∀ v, H 0 v = 1 := fun v => by rw [hH]; simp
      simp only [this, mul_one, Ptr_zero_sum, Finset.range_zero, Finset.prod_empty, le_refl]
    | succ k ih =>
      intro hk
      have hkN : k < T + 1 - 1 := by omega
      rw [step_eq K x0 hK ⟨k, hkN⟩ (H (k + 1))]
      have hHu : ∀ v x, H (k + 1) (Function.update v ⟨k, hkN⟩ x)
          = H k v * Real.exp (L * Y k x) := by
        intro v x
        rw [hH, hH]
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (⟨k, hkN⟩ : Fin (T + 1 - 1))),
          ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (⟨k, hkN⟩ : Fin (T + 1 - 1)))]
        simp only [Function.update_self, lt_add_iff_pos_right, zero_lt_one, if_true,
          lt_irrefl, if_false, one_mul]
        rw [mul_comm]
        congr 1
        refine Finset.prod_congr rfl fun j hj => ?_
        have hjk : j ≠ ⟨k, hkN⟩ := Finset.ne_of_mem_erase hj
        have hjk' : j.1 ≠ k := fun h => hjk (Fin.ext h)
        rw [Function.update_of_ne hjk]
        by_cases hlt : j.1 < k
        · rw [if_pos (by omega), if_pos hlt]
        · rw [if_neg (by omega), if_neg hlt]
      simp only [hHu]
      have hbound : ∀ v, Ptr K x0 k v * ∑ x, K (Function.update v ⟨k, hkN⟩ x) ⟨k, hkN⟩
          * (H k v * Real.exp (L * Y k x))
          ≤ Ptr K x0 k v * H k v * (1 + (Real.exp L - 1) * ((1 - γ) * B k)) := by
        intro v
        have e : ∑ x, K (Function.update v ⟨k, hkN⟩ x) ⟨k, hkN⟩
            * (H k v * Real.exp (L * Y k x))
            = H k v * ∑ x, K (Function.update v ⟨k, hkN⟩ x) ⟨k, hkN⟩
              * Real.exp (L * Y k x) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
        rw [e, mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (Ptr_nonneg K hK0 x0 k v)
        exact mul_le_mul_of_nonneg_left (hstep1 v k (by omega)) (hH0 k v)
      calc _ ≤ ∑ v, Ptr K x0 k v * H k v * (1 + (Real.exp L - 1) * ((1 - γ) * B k)) :=
            Finset.sum_le_sum fun v _ => hbound v
        _ = (∑ v, Ptr K x0 k v * H k v) * (1 + (Real.exp L - 1) * ((1 - γ) * B k)) := by
            rw [Finset.sum_mul]
        _ ≤ (∏ j ∈ Finset.range k, (1 + (Real.exp L - 1) * ((1 - γ) * B j)))
              * (1 + (Real.exp L - 1) * ((1 - γ) * B k)) := by
            refine mul_le_mul_of_nonneg_right (ih (by omega)) ?_
            have := hB0 k (by omega)
            have : 0 ≤ (Real.exp L - 1) * ((1 - γ) * B k) := by positivity
            linarith
        _ = _ := by rw [Finset.prod_range_succ]
  -- the sum of the means is at most `(1 - γ) c`
  have hBsum : ∑ j ∈ Finset.range m, B j ≤ c := by
    have hLP := hy.2.1 i t ht
    refine le_trans ?_ hLP
    have e : ∑ j ∈ Finset.range m, B j = ∑ τ ∈ Finset.Ico 1 t, ∑ z, ∑ S ∈ I.feas,
        I.F τ z * Gbar I z i (t - τ) * I.phi z S i * y τ z S := by
      rw [Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr (by rw [hm]) fun j hj => ?_
      rw [hB]
      have : m - j = t - (1 + j) := by omega
      rw [this]
    rw [e]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro τ hτ; simp only [Finset.mem_Ico] at hτ; simp only [Finset.mem_Icc]; omega
    · intro τ hτ _
      have hτT : τ ∈ Finset.Icc 1 T := by
        simp only [Finset.mem_Icc] at hτ ⊢; omega
      refine Finset.sum_nonneg fun z _ => Finset.sum_nonneg fun S hS => ?_
      have := hy.1 τ hτT z S hS
      have := hI.F_nonneg τ z
      have := hI.phi_nonneg z S hS i
      have := Gbar_nonneg I hI z i (t - τ)
      positivity
  have hprod : ∏ j ∈ Finset.range m, (1 + (Real.exp L - 1) * ((1 - γ) * B j))
      ≤ Real.exp ((Real.exp L - 1) * (1 - γ) * c) := by
    calc _ ≤ ∏ j ∈ Finset.range m, Real.exp ((Real.exp L - 1) * ((1 - γ) * B j)) := by
          refine Finset.prod_le_prod (fun j hj => ?_) (fun j _ => ?_)
          · have := hB0 j (Finset.mem_range.mp hj)
            have : 0 ≤ (Real.exp L - 1) * ((1 - γ) * B j) := by positivity
            linarith
          · linarith [Real.add_one_le_exp ((Real.exp L - 1) * ((1 - γ) * B j))]
      _ = Real.exp (∑ j ∈ Finset.range m, (Real.exp L - 1) * ((1 - γ) * B j)) :=
          (Real.exp_sum _ _).symm
      _ ≤ _ := by
          apply Real.exp_le_exp.mpr
          rw [← Finset.mul_sum, ← Finset.mul_sum]
          have := mul_le_mul_of_nonneg_left hBsum hg1
          have := mul_le_mul_of_nonneg_left this heL
          linarith
  -- Markov's inequality
  set ind : (Fin (T + 1 - 1) → Step n T Z) → ℝ :=
    fun v => if onHand I 1 ret v i m = 0 then 1 else 0 with hind_def
  have hind_dep : DepLt ind m := by
    intro v w hvw
    simp only [hind_def, onHand_congr I 1 ret v w i m hvw]
  have hprob : probNoUnit I y rule 1 ret i t = ∑ v, Ptr K x0 m v * ind v := by
    unfold probNoUnit pathProb
    exact trunc K x0 hK hK1 m hmN.le ind hind_dep
  have hmarkov : ∀ v, ind v ≤ Real.exp (-L * c) * H m v := by
    intro v
    have hHm : H m v = Real.exp (L * ∑ j : Fin (T + 1 - 1),
        if j.1 < m then Y j.1 (v j) else 0) := by
      rw [hH, Finset.mul_sum, Real.exp_sum]
      refine Finset.prod_congr rfl fun j _ => ?_
      split_ifs <;> simp
    have hcount : ((Finset.univ.filter (fun j : Fin (T + 1 - 1) =>
        j.1 < m ∧ (v j).2.2.2.2.1 = some i ∧ m < j.1 + ((v j).2.2.2.2.2 : ℕ))).card : ℝ)
        = ∑ j : Fin (T + 1 - 1), if j.1 < m then Y j.1 (v j) else 0 := by
      rw [Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hY]
      by_cases h1 : j.1 < m
      · simp only [h1, true_and, if_true]
        split_ifs <;> simp
      · simp [h1]
    simp only [hind_def]
    split_ifs with h0
    · have hle : (I.c i : ℝ) ≤ ∑ j : Fin (T + 1 - 1), if j.1 < m then Y j.1 (v j) else 0 := by
        rw [← hcount]
        have : I.c i ≤ (Finset.univ.filter (fun j : Fin (T + 1 - 1) =>
            j.1 < m ∧ (v j).2.2.2.2.1 = some i ∧ m < j.1 + ((v j).2.2.2.2.2 : ℕ))).card := by
          simp only [onHand, hret, Finset.sum_const_zero, Nat.sub_zero] at h0
          omega
        exact_mod_cast this
      rw [hHm, ← Real.exp_add]
      apply Real.one_le_exp
      have := mul_le_mul_of_nonneg_left hle hL0
      rw [hc]; linarith
    · rw [hHm, ← Real.exp_add]; exact (Real.exp_pos _).le
  have hfin : probNoUnit I y rule 1 ret i t ≤ Real.exp (-L * c) * Real.exp ((Real.exp L - 1) * (1 - γ) * c) := by
    rw [hprob]
    calc _ ≤ ∑ v, Ptr K x0 m v * (Real.exp (-L * c) * H m v) :=
          Finset.sum_le_sum fun v _ =>
            mul_le_mul_of_nonneg_left (hmarkov v) (Ptr_nonneg K hK0 x0 m v)
      _ = Real.exp (-L * c) * ∑ v, Ptr K x0 m v * H m v := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by ring
      _ ≤ Real.exp (-L * c) * ∏ j ∈ Finset.range m, (1 + (Real.exp L - 1) * ((1 - γ) * B j)) :=
          mul_le_mul_of_nonneg_left (hind m le_rfl) (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
  rw [← Real.exp_add] at hfin
  rw [hret] at hfin
  refine hfin.trans (Real.exp_le_exp.mpr ?_)
  rw [hc] at hLb
  linarith
