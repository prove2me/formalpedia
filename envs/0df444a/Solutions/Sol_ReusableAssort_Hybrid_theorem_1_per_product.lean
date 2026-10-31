-- Prove2me | solution 1 for ReusableAssort.Hybrid.theorem_1_per_product
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T06:38:08.260468+00:00
-- url     : https://prove2.me/submissions/c1ce9097-a3d1-40a3-8e5d-8bd71f4af42c

import Mathlib
import Definitions.Def_ReusableAssort_Hybrid_Process
import Theorems.Thm_ReusableAssort_Hybrid_proposition_3
import Theorems.Thm_ReusableAssort_Hybrid_eq_EC_2

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

theorem solution {n T : ℕ} {Z : Type} [Fintype Z] [DecidableEq Z]
    (I : Instance n T Z) (hI : I.Assumptions)
    (y : ℕ → Z → Finset (Fin n) → ℝ) (hy : LPFeasible I y) (hN : Normalized I y)
    (rule : Fin n → Rule Z) (hrule : ∀ j, (rule j).Valid)
    (i : Fin n) (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (hi : rule i = Rule.random γ) :
    ∀ t ∈ Finset.Icc 1 T,
      (1 - γ) * (1 - Real.exp (-(γ ^ 2 * (I.c i : ℝ) / (2 - γ))))
          * ∑ z, ∑ S ∈ I.feas, I.F t z * I.r z i * I.phi z S i * y t z S
        ≤ expRevAt I y rule 1 (fun _ _ => 0) i t := by
  classical
  intro t ht
  have hEC := eq_EC_2 I hI y hy hN rule hrule i γ hγ hi t ht
  have ht1 := (Finset.mem_Icc.mp ht).1
  have htT := (Finset.mem_Icc.mp ht).2
  -- a point of the step space
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
  set m := t - 1 with hm
  have hmN : m < T + 1 - 1 := by omega
  obtain ⟨A, hA⟩ : ∃ A, A = ∑ z, ∑ S ∈ I.feas, I.F t z * I.r z i * I.phi z S i * y t z S :=
    ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    rw [hA]
    refine Finset.sum_nonneg fun z _ => Finset.sum_nonneg fun S hS => ?_
    have := hy.1 t ht z S hS
    have := hI.F_nonneg t z
    have := hI.phi_nonneg z S hS i
    have := hI.r_nonneg z i
    positivity
  set ind : (Fin (T + 1 - 1) → Step n T Z) → ℝ :=
    fun v => if onHand I 1 ret v i m = 0 then 1 else 0 with hind
  have hind_dep : DepLt ind m := by
    intro v w hvw
    simp only [hind, onHand_congr I 1 ret v w i m hvw]
  -- total mass
  have hmass : ∑ v, Ptr K x0 m v = 1 := by
    have h1 := trunc K x0 hK hK1 m hmN.le (fun _ => 1) (fun _ _ _ => rfl)
    have h0 := trunc K x0 hK hK1 0 (Nat.zero_le _) (fun _ => 1) (fun _ _ _ => rfl)
    simp only [mul_one] at h1 h0
    rw [← h1, h0, Ptr_zero_sum]
  have hprob : probNoUnit I y rule 1 ret i t = ∑ v, Ptr K x0 m v * ind v := by
    unfold probNoUnit pathProb
    exact trunc K x0 hK hK1 m hmN.le ind hind_dep
  -- the revenue at step `m`
  set rev : (Fin (T + 1 - 1) → Step n T Z) → ℝ := fun v => revAt I 1 i m v with hrev
  have hrev_dep : DepLt rev (m + 1) := by
    intro v w hvw
    simp only [hrev, revAt, dif_pos hmN]
    rw [hvw ⟨m, hmN⟩ (by simp)]
  have hexp : expRevAt I y rule 1 ret i t = ∑ v, Ptr K x0 (m + 1) v * rev v := by
    unfold expRevAt pathProb
    exact trunc K x0 hK hK1 (m + 1) hmN rev hrev_dep
  rw [step_eq K x0 hK ⟨m, hmN⟩ rev] at hexp
  have hinner : ∀ v, ∑ x, K (Function.update v ⟨m, hmN⟩ x) ⟨m, hmN⟩
      * rev (Function.update v ⟨m, hmN⟩ x) = (1 - γ) * A * (1 - ind v) := by
    intro v
    have hrx : ∀ x, rev (Function.update v ⟨m, hmN⟩ x)
        = if x.2.2.2.2.1 = some i then I.r x.1 i else 0 := by
      intro x
      simp only [hrev, revAt, dif_pos hmN, Function.update_self]
    simp only [hKdef, kernel_update, hrx]
    rw [kstep_rev I hI y _ i]
    have h1m : 1 + m = t := by omega
    simp only [aOf, hi, keep, h1m, hind]
    split_ifs with h0
    · simp
    · rw [← Finset.mul_sum, ← hA]; ring
  simp only [hinner] at hexp
  have : expRevAt I y rule 1 ret i t = (1 - γ) * A * (1 - probNoUnit I y rule 1 ret i t) := by
    rw [hexp, hprob]
    have e : ∑ v, Ptr K x0 m v * ((1 - γ) * A * (1 - ind v))
        = (1 - γ) * A * (∑ v, Ptr K x0 m v - ∑ v, Ptr K x0 m v * ind v) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun v _ => by ring
    rw [e, hmass]
  rw [hret] at this hEC
  rw [this, ← hA]
  have hg : 0 ≤ 1 - γ := by linarith [hγ.2]
  have : 1 - Real.exp (-(γ ^ 2 * (I.c i : ℝ) / (2 - γ)))
      ≤ 1 - probNoUnit I y rule 1 (fun _ _ => 0) i t := by linarith
  have := mul_le_mul_of_nonneg_left this (mul_nonneg hg hA0)
  linarith
