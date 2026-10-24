-- Prove2me | solution 1 for OnlineCRS.Submod.selectability_to_approximation
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-24T04:29:12.183619+00:00
-- url     : https://prove2.me/submissions/115ca956-9719-4b3c-aa07-2d811cee2ead

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_OnlineCRS_Matroid_Basics
import Definitions.Def_OnlineCRS_Submod_Model


open scoped BigOperators
namespace OCRSProof
open Finset
variable {α : Type} [Fintype α] [DecidableEq α]

noncomputable def expect (x : α → ℝ) (g : Finset α → ℝ) : ℝ :=
  ∑ A, OnlineCRS.Matroid.activeProb x A * g A

noncomputable def weightOn (U : Finset α) (x : α → ℝ) (A : Finset α) : ℝ :=
  ∏ e ∈ U, if e ∈ A then x e else 1 - x e

noncomputable def expectOn (U : Finset α) (x : α → ℝ) (g : Finset α → ℝ) : ℝ :=
  ∑ A ∈ U.powerset, weightOn U x A * g A

lemma expect_eq_expectOn (x : α → ℝ) (g : Finset α → ℝ) :
    expect x g = expectOn univ x g := by
  simp [expect, expectOn, weightOn, OnlineCRS.Matroid.activeProb]

omit [Fintype α] in
lemma weightOn_nonneg (U : Finset α) (x : α → ℝ)
    (hx : ∀ e ∈ U, 0 ≤ x e ∧ x e ≤ 1) (A : Finset α) : 0 ≤ weightOn U x A := by
  apply prod_nonneg
  intro e he
  split_ifs <;> linarith [(hx e he).1, (hx e he).2]

lemma activeProb_nonneg (x : α → ℝ) (hx : ∀ e, 0 ≤ x e ∧ x e ≤ 1)
    (A : Finset α) : 0 ≤ OnlineCRS.Matroid.activeProb x A := by
  exact weightOn_nonneg univ x (fun e _ => hx e) A

omit [Fintype α] in
lemma weightOn_factor (U : Finset α) (x : α → ℝ) {A : Finset α} (hA : A ⊆ U) :
    weightOn U x A = (∏ e ∈ A, x e) * ∏ e ∈ U \ A, (1 - x e) := by
  rw [weightOn, prod_ite]
  congr 1
  · congr 1
    ext e
    simp only [mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hA h,h⟩⟩
  · congr 1
    ext e
    simp

omit [Fintype α] in
lemma weightOn_sum (U : Finset α) (x : α → ℝ) :
    ∑ A ∈ U.powerset, weightOn U x A = 1 := by
  calc
    _ = ∑ A ∈ U.powerset, (∏ e ∈ A, x e) * ∏ e ∈ U \ A, (1-x e) := by
      apply sum_congr rfl
      intro A hA
      exact weightOn_factor U x (mem_powerset.mp hA)
    _ = ∏ e ∈ U, (x e + (1-x e)) := (Finset.prod_add _ _ _).symm
    _ = 1 := by simp

lemma activeProb_sum (x : α → ℝ) : ∑ A, OnlineCRS.Matroid.activeProb x A = 1 := by
  simpa [weightOn, OnlineCRS.Matroid.activeProb] using weightOn_sum (univ : Finset α) x

lemma expect_const (x : α → ℝ) (a : ℝ) : expect x (fun _ => a) = a := by
  simp [expect, ← sum_mul, activeProb_sum]

lemma expect_add (x : α → ℝ) (f g : Finset α → ℝ) :
    expect x (fun A => f A + g A) = expect x f + expect x g := by
  simp [expect, mul_add, sum_add_distrib]

lemma expect_sub (x : α → ℝ) (f g : Finset α → ℝ) :
    expect x (fun A => f A - g A) = expect x f - expect x g := by
  simp [expect, mul_sub, sum_sub_distrib]

lemma expect_mul (x : α → ℝ) (a : ℝ) (f : Finset α → ℝ) :
    expect x (fun A => a * f A) = a * expect x f := by
  simp [expect, mul_left_comm, mul_sum]

lemma expect_nonneg (x : α → ℝ) (hx : ∀ e, 0 ≤ x e ∧ x e ≤ 1)
    (f : Finset α → ℝ) (hf : ∀ A, 0 ≤ f A) : 0 ≤ expect x f :=
  sum_nonneg fun A _ => mul_nonneg (activeProb_nonneg x hx A) (hf A)

lemma expect_mono (x : α → ℝ) (hx : ∀ e, 0 ≤ x e ∧ x e ≤ 1)
    {f g : Finset α → ℝ} (h : ∀ A, f A ≤ g A) : expect x f ≤ expect x g :=
  sum_le_sum fun A _ => mul_le_mul_of_nonneg_left (h A) (activeProb_nonneg x hx A)

lemma expect_sum {ι : Type} (s : Finset ι) (x : α → ℝ) (f : ι → Finset α → ℝ) :
    expect x (fun A => ∑ i ∈ s, f i A) = ∑ i ∈ s, expect x (f i) := by
  simp only [expect, mul_sum]
  exact sum_comm

lemma native_F (x : α → ℝ) (f : Finset α → ℝ) :
    NonmonotoneSubmod.Shared.F f x = expect x f := by
  simp [NonmonotoneSubmod.Shared.F, expect, OnlineCRS.Matroid.activeProb, mul_comm]

lemma weight_lattice (x : α → ℝ) (A B : Finset α) :
    OnlineCRS.Matroid.activeProb x A * OnlineCRS.Matroid.activeProb x B =
      OnlineCRS.Matroid.activeProb x (A ∩ B) * OnlineCRS.Matroid.activeProb x (A ∪ B) := by
  simp only [OnlineCRS.Matroid.activeProb, ← prod_mul_distrib]
  apply prod_congr rfl
  intro e _
  by_cases ha : e ∈ A <;> by_cases hb : e ∈ B <;> simp [ha,hb, mul_comm]

lemma expect_antitone_mul (x : α → ℝ) (hx : ∀ e, 0 ≤ x e ∧ x e ≤ 1)
    (f g : Finset α → ℝ) (hf0 : ∀ A, 0 ≤ f A) (hg0 : ∀ A, 0 ≤ g A)
    (hf : Antitone f) (hg : Antitone g) : expect x f * expect x g ≤ expect x (fun A => f A*g A) := by
  have h := fkg (α := OrderDual (Finset α))
    (fun A => f (OrderDual.ofDual A)) (fun A => g (OrderDual.ofDual A))
    (fun A => OnlineCRS.Matroid.activeProb x (OrderDual.ofDual A))
    (fun A => activeProb_nonneg x hx _) hf0 hg0
    (fun _ _ h => hf h) (fun _ _ h => hg h)
    (fun A B => by
      change OnlineCRS.Matroid.activeProb x (OrderDual.ofDual A) *
        OnlineCRS.Matroid.activeProb x (OrderDual.ofDual B) ≤
        OnlineCRS.Matroid.activeProb x (OrderDual.ofDual A ∪ OrderDual.ofDual B) *
        OnlineCRS.Matroid.activeProb x (OrderDual.ofDual A ∩ OrderDual.ofDual B)
      rw [weight_lattice]; exact le_of_eq (mul_comm _ _))
  change expect x f * expect x g ≤ (∑ A, OnlineCRS.Matroid.activeProb x A) *
    expect x (fun A => f A * g A) at h
  simpa [activeProb_sum] using h

omit [Fintype α] in
lemma powerset_sum_insert (U : Finset α) {e : α} (he : e ∉ U) (g : Finset α → ℝ) :
    ∑ A ∈ (insert e U).powerset, g A =
      (∑ A ∈ U.powerset, g A) + ∑ A ∈ U.powerset, g (insert e A) := by
  rw [powerset_insert, sum_union]
  · congr 1
    apply sum_image
    intro A hA B hB h
    have ha : e ∉ A := fun h => he (mem_powerset.mp hA h)
    have hb : e ∉ B := fun h => he (mem_powerset.mp hB h)
    have := congrArg (fun S : Finset α => S.erase e) h
    simpa [ha,hb] using this
  · apply disjoint_left.mpr
    intro A hA hAI
    obtain ⟨B,_,rfl⟩ := mem_image.mp hAI
    exact he (mem_powerset.mp hA (mem_insert_self _ _))

omit [Fintype α] in
lemma weightOn_insert_absent (U : Finset α) (x : α → ℝ) {e : α} (he : e ∉ U)
    {A : Finset α} (hA : A ⊆ U) :
    weightOn (insert e U) x A = (1-x e)*weightOn U x A := by
  have ha : e ∉ A := fun h => he (hA h)
  simp [weightOn, he,ha]

omit [Fintype α] in
lemma weightOn_insert_present (U : Finset α) (x : α → ℝ) {e : α} (he : e ∉ U)
    (A : Finset α) :
    weightOn (insert e U) x (insert e A) = x e*weightOn U x A := by
  simp only [weightOn, prod_insert he, mem_insert_self, if_true]
  congr 1
  apply prod_congr rfl
  intro a ha
  have hne : a ≠ e := fun h => he (h ▸ ha)
  simp [hne]

omit [Fintype α] in
lemma expectOn_insert (U : Finset α) (x : α → ℝ) {e : α} (he : e ∉ U)
    (g : Finset α → ℝ) :
    expectOn (insert e U) x g = (1-x e)*expectOn U x g +
      x e*expectOn U x (fun A => g (insert e A)) := by
  unfold expectOn
  rw [powerset_sum_insert U he]
  congr 1
  · rw [mul_sum]
    apply sum_congr rfl
    intro A hA
    rw [weightOn_insert_absent U x he (mem_powerset.mp hA)]
    ring
  · rw [mul_sum]
    apply sum_congr rfl
    intro A _
    rw [weightOn_insert_present U x he]
    ring

lemma expect_indicator_extract (x : α → ℝ) (g : Finset α → ℝ) (e : α)
    (hg : ∀ A, g (insert e A) = g A) :
    expect x (fun A => if e ∈ A then g A else 0) = x e * expect x g := by
  rw [expect_eq_expectOn, expect_eq_expectOn]
  have hu : (univ : Finset α) = insert e (univ.erase e) := (insert_erase (mem_univ e)).symm
  rw [hu, expectOn_insert _ x (notMem_erase e univ), expectOn_insert _ x (notMem_erase e univ)]
  have hz : expectOn (univ.erase e) x (fun A => if e ∈ A then g A else 0) = 0 := by
    apply sum_eq_zero
    intro A hA
    have heA : e ∉ A := fun h => (notMem_erase e univ) (mem_powerset.mp hA h)
    simp [heA]
  simp only [hz, mul_zero, zero_add, mem_insert_self, if_true, hg]
  ring

omit [Fintype α] in
lemma expectOn_const (U : Finset α) (x : α → ℝ) (a : ℝ) :
    expectOn U x (fun _ => a) = a := by
  simp [expectOn, ← sum_mul, weightOn_sum]

omit [Fintype α] in
lemma expectOn_congr (U : Finset α) (x : α → ℝ) {f g : Finset α → ℝ}
    (h : ∀ A, A ⊆ U → f A = g A) : expectOn U x f = expectOn U x g := by
  apply sum_congr rfl
  intro A hA
  rw [h A (mem_powerset.mp hA)]

omit [Fintype α] in
lemma expectOn_indicator (U : Finset α) (x : α → ℝ) (e : α) :
    expectOn U x (fun A => if e ∈ A then (1:ℝ) else 0) = if e ∈ U then x e else 0 := by
  by_cases he : e ∈ U
  · rw [if_pos he, ← insert_erase he, expectOn_insert _ x (notMem_erase e U)]
    have hz : expectOn (U.erase e) x (fun A => if e ∈ A then (1:ℝ) else 0) = 0 := by
      calc
        _ = expectOn (U.erase e) x (fun _ => 0) := by
          apply expectOn_congr
          intro A hA
          have h : e ∉ A := fun h => (notMem_erase e U) (hA h)
          simp [h]
        _ = 0 := expectOn_const _ _ _
    simp [hz, expectOn_const]
  · rw [if_neg he]
    calc
      _ = expectOn U x (fun _ => 0) := by
        apply expectOn_congr
        intro A hA
        have h : e ∉ A := fun h => he (hA h)
        simp [h]
      _ = 0 := expectOn_const _ _ _

omit [Fintype α] in
lemma expectOn_union (U V : Finset α) (hUV : Disjoint U V) (x : α → ℝ)
    (g : Finset α → ℝ) :
    expectOn (U ∪ V) x g = expectOn U x (fun A => expectOn V x (fun B => g (A ∪ B))) := by
  induction U using Finset.induction_on generalizing g with
  | empty => simp [expectOn,weightOn]
  | @insert e U he ih =>
    have heV : e ∉ V := (disjoint_insert_left.mp hUV).1
    have huv : Disjoint U V := (disjoint_insert_left.mp hUV).2
    have heUV : e ∉ U ∪ V := by simp [he,heV]
    rw [insert_union, expectOn_insert _ x heUV, expectOn_insert _ x he,
      ih huv g, ih huv (fun A => g (insert e A))]
    simp [insert_union]

end OCRSProof

namespace OCRSProof
open Classical
open Finset OnlineCRS.Matroid OnlineCRS.Submod
variable {α : Type} [DecidableEq α]

noncomputable def characteristic (Fam : Finset (Finset α)) (A : Finset α) : Finset α :=
  A.filter (fun e => Selectable Fam A e)

lemma selectable_antitone (Fam : Finset (Finset α)) (e : α) {A B : Finset α}
    (hAB : A ⊆ B) (h : Selectable Fam B e) : Selectable Fam A e :=
  fun I hI hIF => h I (hI.trans hAB) hIF

lemma selectable_insert (Fam : Finset (Finset α)) (e : α) (A : Finset α) :
    Selectable Fam (insert e A) e ↔ Selectable Fam A e := by
  constructor
  · exact selectable_antitone Fam e (subset_insert e A)
  · intro h I hI hIF
    by_cases he : e ∈ I
    · simpa [insert_eq_of_mem he] using hIF
    · apply h I _ hIF
      intro a ha
      have := hI ha
      rcases mem_insert.mp this with rfl | haA
      · exact (he ha).elim
      · exact haA

lemma greedy_invariant (Fam : Finset (Finset α)) (A : Finset α) (L : List α)
    (S : Finset α) (hSA : S ⊆ A) (hSF : S ∈ Fam) :
    let T := L.foldl (fun U e => if e ∈ A ∧ insert e U ∈ Fam then insert e U else U) S
    S ⊆ T ∧ T ⊆ A ∧ T ∈ Fam ∧
      ∀ e ∈ L, e ∈ A → Selectable Fam A e → e ∈ T := by
  induction L generalizing S with
  | nil => simp [hSA,hSF]
  | cons a L ih =>
    dsimp only
    let S' := if a ∈ A ∧ insert a S ∈ Fam then insert a S else S
    have hsub : S ⊆ S' := by simp only [S']; split_ifs <;> simp
    have hA : S' ⊆ A := by
      simp only [S']; split_ifs with h
      · exact insert_subset h.1 hSA
      · exact hSA
    have hF : S' ∈ Fam := by
      simp only [S']; split_ifs with h
      · exact h.2
      · exact hSF
    obtain ⟨hs,ha,hf,he⟩ := ih S' hA hF
    refine ⟨hsub.trans hs,ha,hf,?_⟩
    intro e hem hea hes
    rcases List.mem_cons.mp hem with rfl | hem
    · apply hs
      have hchoose : e ∈ A ∧ insert e S ∈ Fam := ⟨hea,hes S hSA hSF⟩
      simp [S',hchoose]
    · exact he e hem hea hes

lemma characteristic_subset_greedy (Fam : Finset (Finset α)) (A : Finset α)
    (L : List α) (hL : IsOrder L) (hF : ∅ ∈ Fam) :
    characteristic Fam A ⊆ greedyRun Fam A L := by
  intro e he
  obtain ⟨heA,hes⟩ := mem_filter.mp (show e ∈ A.filter (fun e => Selectable Fam A e) from he)
  exact (greedy_invariant Fam A L ∅ (empty_subset _) hF).2.2.2 e (hL.2 e) heA hes

noncomputable def pruneStep (f : Finset α → ℝ) (K S : Finset α) (e : α) : Finset α :=
  if e ∈ K ∧ f S < f (insert e S) then insert e S else S

noncomputable def pruneFrom (f : Finset α → ℝ) (K : Finset α) (L : List α)
    (S : Finset α) : Finset α := L.foldl (pruneStep f K) S

noncomputable def prune (f : Finset α → ℝ) (L : List α) (K : Finset α) : Finset α :=
  pruneFrom f K L ∅

lemma pruneFrom_subset (f : Finset α → ℝ) (K : Finset α) (L : List α)
    (S : Finset α) (hS : S ⊆ K) : pruneFrom f K L S ⊆ K := by
  induction L generalizing S with
  | nil => exact hS
  | cons e L ih =>
    apply ih
    unfold pruneStep
    split_ifs with h
    · exact insert_subset h.1 hS
    · exact hS

lemma prune_subset (f : Finset α → ℝ) (L : List α) (K : Finset α) : prune f L K ⊆ K :=
  pruneFrom_subset f K L ∅ (empty_subset _)

lemma diminishing [Fintype α] (f : Finset α → ℝ) (hf : NonmonotoneSubmod.Shared.Submodular f)
    {A B : Finset α} (hAB : A ⊆ B) {e : α} (he : e ∉ B) :
    f (insert e B) - f B ≤ f (insert e A) - f A := by
  have hi : insert e A ∩ B = A := by
    ext a
    simp only [mem_inter, mem_insert]
    constructor
    · rintro ⟨rfl | ha,hb⟩
      · exact (he hb).elim
      · exact ha
    · intro ha
      exact ⟨Or.inr ha,hAB ha⟩
  have hu : insert e A ∪ B = insert e B := by simp [insert_union, union_eq_right.mpr hAB]
  have h := hf (insert e A) B
  rw [hi,hu] at h
  linarith

noncomputable def gain (f : Finset α → ℝ) (A P : Finset α) (e : α) : ℝ :=
  f (insert e (A ∩ P)) - f (A ∩ P)

noncomputable def reward (f : Finset α → ℝ) (A K P : Finset α) : List α → ℝ
  | [] => 0
  | e::L => (if e ∈ K then max 0 (gain f A P e) else 0) + reward f A K (insert e P) L

noncomputable def activeChain (f : Finset α → ℝ) (A P : Finset α) : List α → ℝ
  | [] => 0
  | e::L => (if e ∈ A then gain f A P e else 0) + activeChain f A (insert e P) L

lemma gain_zero (f : Finset α → ℝ) {A P : Finset α} {e : α} (heA : e ∈ A) (heP : e ∈ P) :
    gain f A P e = 0 := by simp [gain,insert_eq_of_mem (mem_inter.mpr ⟨heA,heP⟩)]

lemma prune_step_lower [Fintype α] (f : Finset α → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f) (A K P S : Finset α)
    (hK : K ⊆ A) (hS : S ⊆ A ∩ P) (e : α) :
    f S + (if e ∈ K then max 0 (gain f A P e) else 0) ≤ f (pruneStep f K S e) := by
  by_cases heK : e ∈ K
  · rw [if_pos heK]
    by_cases heP : e ∈ P
    · rw [gain_zero f (hK heK) heP, max_self]
      simp only [add_zero,pruneStep]
      split_ifs with h
      · exact h.2.le
      · exact le_rfl
    · have hg : gain f A P e ≤ f (insert e S)-f S :=
        diminishing f hf hS (fun h => heP (mem_inter.mp h).2)
      unfold pruneStep
      split_ifs with h
      · have : max 0 (gain f A P e) ≤ f (insert e S)-f S :=
          max_le (by linarith [h.2]) hg
        linarith
      · have hle : f (insert e S) ≤ f S := le_of_not_gt (fun hh => h ⟨heK,hh⟩)
        have : gain f A P e ≤ 0 := by linarith
        simp [max_eq_left this]
  · simp [pruneStep,heK]

lemma prune_step_prefix (f : Finset α → ℝ) (A K P S : Finset α)
    (hK : K ⊆ A) (hS : S ⊆ A ∩ P) (e : α) :
    pruneStep f K S e ⊆ A ∩ insert e P := by
  unfold pruneStep
  split_ifs with h
  · intro a ha
    rcases mem_insert.mp ha with rfl | ha
    · exact mem_inter.mpr ⟨hK h.1,mem_insert_self _ _⟩
    · obtain ⟨haA,haP⟩ := mem_inter.mp (hS ha)
      exact mem_inter.mpr ⟨haA,mem_insert_of_mem haP⟩
  · exact hS.trans (inter_subset_inter (Subset.refl A) (subset_insert e P))

lemma pruneFrom_lower [Fintype α] (f : Finset α → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f) (A K P S : Finset α)
    (hK : K ⊆ A) (hS : S ⊆ A ∩ P) (L : List α) :
    f S + reward f A K P L ≤ f (pruneFrom f K L S) := by
  induction L generalizing P S with
  | nil => simp [reward,pruneFrom]
  | cons e L ih =>
    have h1 := prune_step_lower f hf A K P S hK hS e
    have h2 := ih (insert e P) (pruneStep f K S e) (prune_step_prefix f A K P S hK hS e)
    simp only [reward,pruneFrom,List.foldl_cons] at *
    linarith

lemma activeChain_telescope (f : Finset α → ℝ) (A P : Finset α) (L : List α) :
    activeChain f A P L = f (A ∩ (P ∪ L.toFinset)) - f (A ∩ P) := by
  induction L generalizing P with
  | nil => simp [activeChain]
  | cons e L ih =>
    rw [activeChain,ih]
    have hu : insert e P ∪ L.toFinset = P ∪ (e::L).toFinset := by ext a; simp
    rw [hu]
    by_cases he : e ∈ A
    · have hi : A ∩ insert e P = insert e (A ∩ P) := by ext a; simp [he]
      rw [if_pos he,hi]
      unfold gain
      ring
    · have hi : A ∩ insert e P = A ∩ P := by ext a; by_cases ha : a=e <;> simp_all
      rw [if_neg he,hi]
      ring

lemma gain_antitone [Fintype α] (f : Finset α → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f) (P : Finset α) {e : α} (he : e ∉ P) :
    Antitone (fun A => max 0 (gain f A P e)) := by
  intro A B hAB
  apply max_le_max le_rfl
  exact diminishing f hf (inter_subset_inter hAB (Subset.refl P)) (fun h => he (mem_inter.mp h).2)

lemma gain_insert (f : Finset α → ℝ) (A P : Finset α) {e : α} (he : e ∉ P) :
    gain f (insert e A) P e = gain f A P e := by
  have hi : insert e A ∩ P = A ∩ P := by ext a; by_cases ha : a=e <;> simp_all
  simp [gain,hi]

end OCRSProof

namespace OCRSProof
open Classical Finset OnlineCRS.Matroid
variable {α : Type} [Fintype α] [DecidableEq α]

noncomputable def selectWeight (w : Finset (Finset α) → ℝ) (e : α) (A : Finset α) : ℝ :=
  ∑ Fam, w Fam * if Selectable Fam A e then 1 else 0

lemma selectWeight_nonneg (w : Finset (Finset α) → ℝ) (hw : ∀ Fam, 0 ≤ w Fam)
    (e : α) (A : Finset α) : 0 ≤ selectWeight w e A := by
  apply sum_nonneg
  intro Fam _
  split_ifs <;> simp_all

lemma selectWeight_antitone (w : Finset (Finset α) → ℝ) (hw : ∀ Fam, 0 ≤ w Fam)
    (e : α) : Antitone (selectWeight w e) := by
  intro A B hAB
  apply sum_le_sum
  intro Fam _
  by_cases hb : Selectable Fam B e
  · have ha := selectable_antitone Fam e hAB hb
    simp [ha,hb]
  · simp [hb]
    split_ifs <;> simp [hw]

lemma selectWeight_insert (w : Finset (Finset α) → ℝ) (e : α) (A : Finset α) :
    selectWeight w e (insert e A) = selectWeight w e A := by
  simp [selectWeight,selectable_insert]

lemma expect_selectWeight (w : Finset (Finset α) → ℝ) (x : α → ℝ) (e : α) :
    expect x (selectWeight w e) = ∑ Fam, w Fam * selProb x Fam e := by
  unfold selectWeight
  rw [expect_sum]
  apply sum_congr rfl
  intro Fam _
  rw [expect_mul]
  congr 1
  simp [expect,selProb,mul_ite]

lemma characteristic_term (w : Finset (Finset α) → ℝ) (x : α → ℝ) (e : α)
    (m : Finset α → ℝ) :
    (∑ Fam, w Fam * expect x (fun A => if e ∈ characteristic Fam A then m A else 0)) =
      expect x (fun A => if e ∈ A then selectWeight w e A * m A else 0) := by
  simp only [expect,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro A _
  by_cases he : e ∈ A
  · simp only [characteristic,mem_filter,he,true_and,if_true,selectWeight,sum_mul,mul_sum]
    apply sum_congr rfl
    intro Fam _
    split_ifs <;> ring
  · simp [characteristic,he]

lemma one_increment (w : Finset (Finset α) → ℝ) (hw : ∀ Fam, 0 ≤ w Fam)
    (x : α → ℝ) (hx : ∀ e, 0 ≤ x e ∧ x e ≤ 1) (c : ℝ) (hc : 0 ≤ c)
    (hsel : ∀ e, c ≤ ∑ Fam, w Fam * selProb x Fam e)
    (f : Finset α → ℝ) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (P : Finset α) (e : α) :
    c * expect x (fun A => if e ∈ A then gain f A P e else 0) ≤
      ∑ Fam, w Fam * expect x (fun A => if e ∈ characteristic Fam A then max 0 (gain f A P e) else 0) := by
  rw [characteristic_term]
  by_cases he : e ∈ P
  · have hleft : (fun A : Finset α => if e ∈ A then gain f A P e else 0) = fun _ => 0 := by
      funext A
      split_ifs with h
      · exact gain_zero f h he
      · rfl
    have hright : (fun A : Finset α => if e ∈ A then selectWeight w e A * max 0 (gain f A P e) else 0) = fun _ => 0 := by
      funext A
      split_ifs with h
      · simp [gain_zero f h he]
      · rfl
    rw [hleft,hright]
    simp [expect_const]
  · rw [expect_indicator_extract x (fun A => gain f A P e) e (fun A => gain_insert f A P he)]
    rw [expect_indicator_extract x (fun A => selectWeight w e A * max 0 (gain f A P e)) e
      (fun A => by rw [selectWeight_insert,gain_insert f A P he])]
    have hq := hsel e
    rw [← expect_selectWeight] at hq
    have hm : 0 ≤ expect x (fun A => max 0 (gain f A P e)) :=
      expect_nonneg x hx _ (fun _ => le_max_left _ _)
    have hmg : expect x (fun A => gain f A P e) ≤ expect x (fun A => max 0 (gain f A P e)) :=
      expect_mono x hx (fun _ => le_max_right _ _)
    have hfk := expect_antitone_mul x hx (selectWeight w e) (fun A => max 0 (gain f A P e))
      (selectWeight_nonneg w hw e) (fun _ => le_max_left _ _) (selectWeight_antitone w hw e)
      (gain_antitone f hf P he)
    have h1 := mul_le_mul_of_nonneg_left hmg hc
    have h2 := mul_le_mul_of_nonneg_right hq hm
    have h3 := mul_le_mul_of_nonneg_left ((h1.trans h2).trans hfk) (hx e).1
    nlinarith

lemma reward_expectation (w : Finset (Finset α) → ℝ) (hw : ∀ Fam, 0 ≤ w Fam)
    (x : α → ℝ) (hx : ∀ e, 0 ≤ x e ∧ x e ≤ 1) (c : ℝ) (hc : 0 ≤ c)
    (hsel : ∀ e, c ≤ ∑ Fam, w Fam * selProb x Fam e)
    (f : Finset α → ℝ) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (P : Finset α) (L : List α) :
    c * expect x (fun A => activeChain f A P L) ≤
      ∑ Fam, w Fam * expect x (fun A => reward f A (characteristic Fam A) P L) := by
  induction L generalizing P with
  | nil => simp [activeChain,reward,expect_const]
  | cons e L ih =>
    have h1 := one_increment w hw x hx c hc hsel f hf P e
    have h2 := ih (insert e P)
    simp only [activeChain,reward,expect_add,mul_add,sum_add_distrib]
    exact add_le_add h1 h2

lemma pruning_expectation (w : Finset (Finset α) → ℝ)
    (hw : ∀ Fam, 0 ≤ w Fam) (hsum : ∑ Fam, w Fam = 1)
    (x : α → ℝ) (hx : ∀ e, 0 ≤ x e ∧ x e ≤ 1)
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hsel : ∀ e, c ≤ ∑ Fam, w Fam * selProb x Fam e)
    (f : Finset α → ℝ) (hf0 : ∀ A, 0 ≤ f A)
    (hf : NonmonotoneSubmod.Shared.Submodular f)
    (L : List α) (hL : ∀ e, e ∈ L) :
    c * NonmonotoneSubmod.Shared.F f x ≤
      ∑ Fam, w Fam * expect x (fun A => f (prune f L (characteristic Fam A))) := by
  have hre := reward_expectation w hw x hx c hc0 hsel f hf ∅ L
  have hfull : L.toFinset = univ := by ext e; simp [hL e]
  have hchain : (fun A : Finset α => activeChain f A ∅ L) = fun A => f A - f ∅ := by
    funext A
    simp [activeChain_telescope,hfull]
  rw [hchain,expect_sub,expect_const] at hre
  have hpoint : ∀ Fam, expect x (fun A => f ∅ + reward f A (characteristic Fam A) ∅ L) ≤
      expect x (fun A => f (prune f L (characteristic Fam A))) := by
    intro Fam
    apply expect_mono x hx
    intro A
    exact pruneFrom_lower f hf A (characteristic Fam A) ∅ ∅
      (filter_subset _ _) (empty_subset _) L
  have hsumle := sum_le_sum (s:=univ) (fun Fam _ => mul_le_mul_of_nonneg_left (hpoint Fam) (hw Fam))
  simp only [expect_add,expect_const,mul_add,sum_add_distrib,← sum_mul,hsum,one_mul] at hsumle
  have hbase : c * f ∅ ≤ f ∅ := by nlinarith [hf0 ∅]
  rw [native_F]
  linarith

end OCRSProof

set_option autoImplicit false

namespace OCRSProof
namespace Correlated

variable {α : Type} [Fintype α] [DecidableEq α]

noncomputable def lawMean (μ : Finset α → ℝ) (g : Finset α → ℝ) : ℝ :=
  ∑ S, μ S * g S

noncomputable def marginal (μ : Finset α → ℝ) (e : α) : ℝ :=
  lawMean μ (fun S => if e ∈ S then 1 else 0)

noncomputable def chainSum (f : Finset α → ℝ) (p : α → ℝ)
    (B : Finset α) : List α → ℝ
  | [] => 0
  | e :: L => (f (insert e B) - f B) * p e + chainSum f p (insert e B) L

lemma diminishing (f : Finset α → ℝ) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (B S : Finset α) (e : α) (he : e ∉ S) :
    f (insert e (B ∪ S)) - f (insert e B) ≤ f (B ∪ S) - f B := by
  have h := hf (insert e B) (B ∪ S)
  have hu : insert e B ∪ (B ∪ S) = insert e (B ∪ S) := by ext x; simp
  have hi : insert e B ∩ (B ∪ S) = B := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_insert]
    aesop
  rw [hu, hi] at h
  linarith

omit [Fintype α] in
lemma chain_congr_outside (f : Finset α → ℝ) (p q : α → ℝ)
    (L : List α) (B : Finset α) (h : ∀ e, e ∉ B → p e = q e) :
    chainSum f p B L = chainSum f q B L := by
  induction L generalizing B with
  | nil => rfl
  | cons e L ih =>
    simp only [chainSum]
    have ht := ih (insert e B) (fun a ha => h a (fun hb => ha (Finset.mem_insert_of_mem hb)))
    rw [ht]
    by_cases he : e ∈ B
    · simp [Finset.insert_eq_of_mem he]
    · rw [h e he]

lemma modular_lower (f : Finset α → ℝ) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (L : List α) (B S : Finset α) (hS : S ⊆ L.toFinset) :
    chainSum f (fun e => if e ∈ S then 1 else 0) B L ≤ f (B ∪ S) - f B := by
  induction L generalizing B S with
  | nil =>
    have : S = ∅ := by simpa using hS
    simp [chainSum, this]
  | cons e L ih =>
    by_cases he : e ∈ S
    · have hsub : S.erase e ⊆ L.toFinset := by
        intro x hx
        have := hS (Finset.mem_of_mem_erase hx)
        simp only [List.toFinset_cons, Finset.mem_insert] at this
        exact this.resolve_left (Finset.ne_of_mem_erase hx)
      have h := ih (insert e B) (S.erase e) hsub
      have hu : insert e B ∪ S.erase e = B ∪ S := by
        ext x
        by_cases hx : x = e
        · subst x; simp [he]
        · simp [hx]
      have hc : chainSum f (fun x => if x ∈ S.erase e then 1 else 0) (insert e B) L =
          chainSum f (fun x => if x ∈ S then 1 else 0) (insert e B) L := by
        apply chain_congr_outside
        intro a ha
        have hae : a ≠ e := fun h => ha (h ▸ Finset.mem_insert_self e B)
        simp [hae]
      rw [hu, hc] at h
      simp only [chainSum, if_pos he, mul_one]
      linarith
    · have hsub : S ⊆ L.toFinset := by
        intro x hx
        have := hS hx
        simp only [List.toFinset_cons, Finset.mem_insert] at this
        rcases this with rfl | h
        · exact (he hx).elim
        · exact h
      have h := ih (insert e B) S hsub
      have hd := diminishing f hf B S e he
      simp only [chainSum, if_neg he, mul_zero, zero_add]
      exact h.trans (by simpa [Finset.insert_union] using hd)

omit [Fintype α] in
lemma chain_constant (f : Finset α → ℝ) (p : ℝ) (L : List α) (B : Finset α) :
    chainSum f (fun _ => p) B L = (f (B ∪ L.toFinset) - f B) * p := by
  induction L generalizing B with
  | nil => simp [chainSum]
  | cons e L ih =>
    simp only [chainSum, ih, List.toFinset_cons]
    rw [Finset.union_insert, Finset.insert_union]
    ring

omit [Fintype α] in
lemma chain_sorted_lower (f : Finset α → ℝ) (hf0 : ∀ S, 0 ≤ f S)
    (p : α → ℝ) (L : List α) (B : Finset α) (u : ℝ)
    (hu : 0 ≤ u) (hp : ∀ e ∈ L, 0 ≤ p e ∧ p e ≤ u)
    (hs : L.Pairwise (fun a b => p b ≤ p a)) :
    -u * f B ≤ chainSum f p B L := by
  induction L generalizing B u with
  | nil => simpa [chainSum] using mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hu) (hf0 B)
  | cons e L ih =>
    have he := hp e (List.mem_cons_self)
    have ht := List.pairwise_cons.mp hs
    have h := ih (insert e B) (p e) he.1
      (fun a ha => ⟨(hp a (List.mem_cons_of_mem e ha)).1, ht.1 a ha⟩) ht.2
    have hb := mul_le_mul_of_nonneg_right he.2 (hf0 B)
    simp only [chainSum]
    nlinarith

lemma mean_chain (μ : Finset α → ℝ) (f : Finset α → ℝ) (L : List α) (B : Finset α) :
    lawMean μ (fun S => chainSum f (fun e => if e ∈ S then 1 else 0) B L) =
      chainSum f (marginal μ) B L := by
  induction L generalizing B with
  | nil => simp [lawMean, chainSum]
  | cons e L ih =>
    simp only [lawMean, chainSum, mul_add, Finset.sum_add_distrib]
    rw [show (∑ S, μ S * chainSum f (fun e => if e ∈ S then 1 else 0) (insert e B) L) =
      chainSum f (marginal μ) (insert e B) L from ih (insert e B)]
    congr 1
    simp only [marginal, lawMean, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    ring

omit [Fintype α] in
lemma chain_congr_mem (f : Finset α → ℝ) (p q : α → ℝ) (L : List α)
    (B : Finset α) (h : ∀ e ∈ L, p e = q e) :
    chainSum f p B L = chainSum f q B L := by
  induction L generalizing B with
  | nil => rfl
  | cons e L ih =>
    simp only [chainSum, h e List.mem_cons_self]
    rw [ih (insert e B) (fun a ha => h a (List.mem_cons_of_mem e ha))]

lemma marginal_nonneg (μ : Finset α → ℝ) (hμ : ∀ S, 0 ≤ μ S) (e : α) :
    0 ≤ marginal μ e := by
  apply Finset.sum_nonneg
  intro S _
  exact mul_nonneg (hμ S) (by dsimp; split_ifs <;> norm_num)

lemma mean_modular_lower (μ : Finset α → ℝ) (hμ : ∀ S, 0 ≤ μ S)
    (hμsum : ∑ S, μ S = 1) (f : Finset α → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f) (L : List α)
    (hsupport : ∀ S, μ S ≠ 0 → S ⊆ L.toFinset) :
    f ∅ + chainSum f (marginal μ) ∅ L ≤ lawMean μ f := by
  have h : lawMean μ (fun S => chainSum f (fun e => if e ∈ S then 1 else 0) ∅ L) ≤
      lawMean μ (fun S => f S - f ∅) := by
    apply Finset.sum_le_sum
    intro S _
    by_cases hz : μ S = 0
    · simp [hz]
    · apply mul_le_mul_of_nonneg_left _ (hμ S)
      simpa using modular_lower f hf L ∅ S (hsupport S hz)
  rw [mean_chain] at h
  have hm : lawMean μ (fun S => f S - f ∅) = lawMean μ f - f ∅ := by
    simp only [lawMean, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hμsum, one_mul]
  rw [hm] at h
  linarith

lemma equal_marginal_lower (μ : Finset α → ℝ) (hμ : ∀ S, 0 ≤ μ S)
    (hμsum : ∑ S, μ S = 1) (f : Finset α → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f) (T : Finset α) (p : ℝ)
    (hsupport : ∀ S, μ S ≠ 0 → S ⊆ T)
    (hmarg : ∀ e ∈ T, marginal μ e = p) :
    (1-p)*f ∅ + p*f T ≤ lawMean μ f := by
  have h := mean_modular_lower μ hμ hμsum f hf T.toList (by simpa using hsupport)
  rw [chain_congr_mem f (marginal μ) (fun _ => p) T.toList ∅
    (by simpa using hmarg), chain_constant] at h
  simp only [Finset.toList_toFinset, Finset.empty_union] at h
  nlinarith

lemma bounded_marginal_lower (μ : Finset α → ℝ) (hμ : ∀ S, 0 ≤ μ S)
    (hμsum : ∑ S, μ S = 1) (f : Finset α → ℝ)
    (hf0 : ∀ S, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (p : ℝ) (hp : 0 ≤ p) (hmarg : ∀ e, marginal μ e ≤ p) :
    (1-p)*f ∅ ≤ lawMean μ f := by
  classical
  let cmp : α → α → Bool := fun a b => decide (marginal μ b ≤ marginal μ a)
  let L := (Finset.univ : Finset α).toList.mergeSort cmp
  have hperm : L.Perm (Finset.univ : Finset α).toList := List.mergeSort_perm _ _
  have hfull : L.toFinset = Finset.univ := by
    ext e
    simpa using hperm.mem_iff
  have hsort : L.Pairwise (fun a b => marginal μ b ≤ marginal μ a) := by
    have h := List.pairwise_mergeSort (le := cmp)
      (fun a b c hab hbc => by
        simp only [cmp, decide_eq_true_eq] at *
        exact hbc.trans hab)
      (fun a b => by simp only [cmp, Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _)
      (Finset.univ : Finset α).toList
    simpa only [cmp, decide_eq_true_eq] using h
  have h := mean_modular_lower μ hμ hμsum f hf L (fun S _ => by rw [hfull]; exact Finset.subset_univ S)
  have hc := chain_sorted_lower f hf0 (marginal μ) L ∅ p hp
    (fun e _ => ⟨marginal_nonneg μ hμ e, hmarg e⟩) hsort
  nlinarith

variable {Ω : Type} [Fintype Ω]

noncomputable def pushLaw (a : Ω → ℝ) (R : Ω → Finset α) (S : Finset α) : ℝ :=
  ∑ ω, if R ω = S then a ω else 0

omit [Fintype α] in
lemma pushLaw_nonneg (a : Ω → ℝ) (ha : ∀ ω, 0 ≤ a ω) (R : Ω → Finset α) :
    ∀ S, 0 ≤ pushLaw a R S := by
  intro S
  apply Finset.sum_nonneg
  intro ω _
  split_ifs
  · exact ha ω
  · exact le_rfl

lemma pushLaw_mean (a : Ω → ℝ) (R : Ω → Finset α) (f : Finset α → ℝ) :
    lawMean (pushLaw a R) f = ∑ ω, a ω * f (R ω) := by
  classical
  simp only [lawMean, pushLaw, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

lemma pushLaw_sum (a : Ω → ℝ) (R : Ω → Finset α) :
    ∑ S, pushLaw a R S = ∑ ω, a ω := by
  simpa [lawMean] using pushLaw_mean a R (fun _ => 1)

lemma equal_marginal_outcomes (a : Ω → ℝ) (ha : ∀ ω, 0 ≤ a ω)
    (hasum : ∑ ω, a ω = 1) (R : Ω → Finset α)
    (f : Finset α → ℝ) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (T : Finset α) (p : ℝ) (hsub : ∀ ω, a ω ≠ 0 → R ω ⊆ T)
    (hmarg : ∀ e ∈ T, (∑ ω, a ω * (if e ∈ R ω then 1 else 0)) = p) :
    (1-p)*f ∅ + p*f T ≤ ∑ ω, a ω * f (R ω) := by
  rw [← pushLaw_mean]
  apply equal_marginal_lower (pushLaw a R) (pushLaw_nonneg a ha R)
    (by rw [pushLaw_sum, hasum]) f hf T p
  · intro S hS
    by_contra h
    apply hS
    apply Finset.sum_eq_zero
    intro ω _
    by_cases he : R ω = S
    · have hz : a ω = 0 := by
        by_contra hz
        exact h (he ▸ hsub ω hz)
      simp [he, hz]
    · simp [he]
  · intro e he
    simpa [marginal, pushLaw_mean] using hmarg e he

lemma bounded_marginal_outcomes (a : Ω → ℝ) (ha : ∀ ω, 0 ≤ a ω)
    (hasum : ∑ ω, a ω = 1) (R : Ω → Finset α)
    (f : Finset α → ℝ) (hf0 : ∀ S, 0 ≤ f S)
    (hf : NonmonotoneSubmod.Shared.Submodular f) (p : ℝ) (hp : 0 ≤ p)
    (hmarg : ∀ e, (∑ ω, a ω * (if e ∈ R ω then 1 else 0)) ≤ p) :
    (1-p)*f ∅ ≤ ∑ ω, a ω * f (R ω) := by
  rw [← pushLaw_mean]
  apply bounded_marginal_lower (pushLaw a R) (pushLaw_nonneg a ha R)
    (by rw [pushLaw_sum, hasum]) f hf0 hf p hp
  intro e
  simpa [marginal, pushLaw_mean] using hmarg e

end Correlated
end OCRSProof

set_option autoImplicit false

namespace OCRSProof
namespace Thinning

open Finset
variable {α : Type} [Fintype α] [DecidableEq α]

noncomputable def lawOn (U : Finset α) (x : α → ℝ) (A : Finset α) : ℝ :=
  if A ⊆ U then weightOn U x A else 0

lemma lawOn_mean (U : Finset α) (x : α → ℝ) (f : Finset α → ℝ) :
    Correlated.lawMean (lawOn U x) f = expectOn U x f := by
  classical
  simp only [Correlated.lawMean, lawOn, ite_mul, zero_mul, expectOn]
  rw [← sum_filter]
  congr 1
  ext A
  simp

omit [Fintype α] in
lemma lawOn_nonneg (U : Finset α) (x : α → ℝ)
    (hx : ∀ e ∈ U, 0 ≤ x e ∧ x e ≤ 1) : ∀ A, 0 ≤ lawOn U x A := by
  intro A
  unfold lawOn
  split_ifs
  · exact weightOn_nonneg U x hx A
  · exact le_rfl

lemma lawOn_sum (U : Finset α) (x : α → ℝ) : ∑ A, lawOn U x A = 1 := by
  have h := lawOn_mean U x (fun _ => 1)
  simpa [Correlated.lawMean, expectOn, weightOn_sum] using h.trans (by simp [expectOn, weightOn_sum])

omit [Fintype α] in
lemma expectOn_const (U : Finset α) (x : α → ℝ) (a : ℝ) :
    expectOn U x (fun _ => a) = a := by
  simp [expectOn, ← sum_mul, weightOn_sum]

omit [Fintype α] in
lemma expectOn_mono (U : Finset α) (x : α → ℝ)
    (hx : ∀ e ∈ U, 0 ≤ x e ∧ x e ≤ 1) {f g : Finset α → ℝ}
    (h : ∀ A, A ⊆ U → f A ≤ g A) : expectOn U x f ≤ expectOn U x g := by
  apply sum_le_sum
  intro A hA
  exact mul_le_mul_of_nonneg_left (h A (mem_powerset.mp hA)) (weightOn_nonneg U x hx A)

omit [Fintype α] in
lemma expectOn_mul (U : Finset α) (x : α → ℝ) (a : ℝ) (f : Finset α → ℝ) :
    expectOn U x (fun A => a*f A) = a * expectOn U x f := by
  simp [expectOn, mul_sum, mul_left_comm]

lemma union_submodular (f : Finset α → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f) (B : Finset α) :
    NonmonotoneSubmod.Shared.Submodular (fun U => f (B ∪ U)) := by
  intro U V
  simpa [union_assoc, union_left_comm, union_inter_distrib_left] using hf (B ∪ U) (B ∪ V)

lemma fair_subset_chord (f : Finset α → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f) (T : Finset α) :
    (1/2:ℝ)*f ∅ + (1/2:ℝ)*f T ≤ expectOn T (fun _ => (1/2:ℝ)) f := by
  rw [← lawOn_mean]
  have h := Correlated.equal_marginal_lower (lawOn T (fun _ => (1/2:ℝ)))
    (lawOn_nonneg T _ (by intro e he; norm_num)) (lawOn_sum T _) f hf T (1/2)
  apply (by norm_num at h; exact h)
  · intro A hA
    by_contra h
    exact hA (by simp [lawOn, h])
  · intro e he
    rw [Correlated.marginal, lawOn_mean, OCRSProof.expectOn_indicator]
    simp [he]

lemma conditional_half (f : Finset α → ℝ) (hf0 : ∀ A, 0 ≤ f A)
    (hf : NonmonotoneSubmod.Shared.Submodular f) (B U : Finset α)
    (S : Finset α → Finset α) (hB : ∀ C, C ⊆ U → B ⊆ S (B ∪ C)) :
    f B / 2 ≤ expectOn U (fun _ => (1/2:ℝ))
      (fun C => f (S (B ∪ C) ∩ (B ∪ C))) := by
  let a := lawOn U (fun _ => (1/2:ℝ))
  let R := fun C => S (B ∪ C) ∩ C
  have h := Correlated.bounded_marginal_outcomes a
    (lawOn_nonneg U _ (by intro e he; norm_num)) (lawOn_sum U _) R
    (fun D => f (B ∪ D)) (fun D => hf0 _) (union_submodular f hf B) (1/2)
    (by norm_num) (by
      intro e
      change Correlated.lawMean a (fun C => if e ∈ R C then 1 else 0) ≤ (1/2:ℝ)
      rw [show a = lawOn U (fun _ => (1/2:ℝ)) from rfl, lawOn_mean]
      calc
        _ ≤ expectOn U (fun _ => (1/2:ℝ)) (fun C => if e ∈ C then 1 else 0) := by
          apply expectOn_mono U _ (by intro j hj; norm_num)
          intro C hC
          dsimp [R]
          split_ifs <;> simp_all
        _ ≤ 1/2 := by rw [OCRSProof.expectOn_indicator]; split_ifs <;> norm_num)
  change (1-(1/2:ℝ))*f (B ∪ ∅) ≤ Correlated.lawMean a (fun C => f (B ∪ R C)) at h
  rw [show a = lawOn U (fun _ => (1/2:ℝ)) from rfl, lawOn_mean] at h
  have heq : expectOn U (fun _ => (1/2:ℝ)) (fun C => f (B ∪ R C)) =
      expectOn U (fun _ => (1/2:ℝ)) (fun C => f (S (B ∪ C) ∩ (B ∪ C))) := by
    apply OCRSProof.expectOn_congr
    intro C hC
    congr 1
    dsimp [R]
    ext e
    simp only [mem_union, mem_inter]
    have hb := hB C hC
    aesop
  rw [heq] at h
  norm_num at h ⊢
  linarith

lemma almighty_thinning (f : Finset α → ℝ) (hf0 : ∀ A, 0 ≤ f A)
    (hf : NonmonotoneSubmod.Shared.Submodular f) (T : Finset α)
    (S : Finset α → Finset α) (hT : ∀ C, T ⊆ S C) :
    f T / 4 ≤ expect (fun _ => (1/2:ℝ)) (fun C => f (S C ∩ C)) := by
  rw [expect_eq_expectOn]
  have hu : (univ : Finset α) = T ∪ (univ \ T) := by ext e; simp
  rw [hu, OCRSProof.expectOn_union T (univ \ T) (disjoint_sdiff)]
  have hinner : expectOn T (fun _ => (1/2:ℝ)) (fun B => f B / 2) ≤
      expectOn T (fun _ => (1/2:ℝ)) (fun B =>
        expectOn (univ \ T) (fun _ => (1/2:ℝ)) (fun C => f (S (B ∪ C) ∩ (B ∪ C)))) := by
    apply expectOn_mono T _ (by intro e he; norm_num)
    intro B hB
    apply conditional_half f hf0 hf B (univ \ T) S
    intro C _
    exact hB.trans (hT _)
  have hchord := fair_subset_chord f hf T
  have hbase := hf0 ∅
  have hscale : expectOn T (fun _ => (1/2:ℝ)) (fun B => f B / 2) =
      (1/2:ℝ) * expectOn T (fun _ => (1/2:ℝ)) f := by
    simpa [div_eq_mul_inv, mul_comm] using expectOn_mul T (fun _ => (1/2:ℝ)) (1/2) f
  rw [hscale] at hinner
  linarith

end Thinning
end OCRSProof

open scoped Pointwise
namespace OnlineCRS.Submod

/-- Theorem 1.10 (arXiv:1508.00142v2, p. 5, restated p. 16): let `P ⊆ [0,1]^N` be a relaxation of the
down-closed feasible sets `𝓕`, `w` a `(b, c)`-selectable (randomized) greedy OCRS for `P`, `x ∈ bP`, and
`f ≥ 0` submodular with multilinear extension `F`. Against every almighty adversary:
(i) if `f` is monotone, the selected set `S` satisfies `E[f(S)] ≥ c · F(x)`;
(ii) without monotonicity, `E[f(S(1/2))] ≥ (c/4) · F(x)`, where the coins defining `S(1/2)` are known to
the adversary. -/
theorem selectability_to_approximation {α : Type} [Fintype α] [DecidableEq α]
    (𝓕 : Finset α → Prop) (P : Set (α → ℝ))
    (hPoly : IsPolytope P) (hRel : IsRelaxation 𝓕 P)
    (b c : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (w : (α → ℝ) → Finset (Finset α) → ℝ) (hw : OnlineCRS.Matroid.IsSelectableRand 𝓕 P b c w)
    (x : α → ℝ) (hx : x ∈ b • P)
    (f : Finset α → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f) :
    ((∀ A B : Finset α, A ⊆ B → f A ≤ f B) →
        ∀ ord : Finset (Finset α) → Finset α → List α, (∀ Fam A, IsOrder (ord Fam A)) →
          c * NonmonotoneSubmod.Shared.F f x ≤ expOutput w x ord f) ∧
      (∀ ord : Finset (Finset α) → Finset α → Finset α → List α,
        (∀ Fam A C, IsOrder (ord Fam A C)) →
          c / 4 * NonmonotoneSubmod.Shared.F f x ≤ expOutputHalf w x ord f) := by
  classical
  have _hPoly := hPoly
  have hx01 : ∀ e, 0 ≤ x e ∧ x e ≤ 1 := by
    rcases hx with ⟨y,hy,rfl⟩
    intro e
    change 0 ≤ b * y e ∧ b * y e ≤ 1
    have he := hRel.2.1 y hy e
    constructor
    · exact mul_nonneg hb0 he.1
    · nlinarith
  let L := (Finset.univ : Finset α).toList
  have hL : ∀ e, e ∈ L := by intro e; simp [L]
  have hw0 := (hw.1 x).1
  have hws := (hw.1 x).2.1
  have hpr := OCRSProof.pruning_expectation (w x) hw0 hws x hx01 c hc0 hc1
    (hw.2 x hx) f hf0 hf L hL
  have hcontain : ∀ Fam, w x Fam ≠ 0 → ∀ A σ, IsOrder σ →
      OCRSProof.prune f L (OCRSProof.characteristic Fam A) ⊆ greedyRun Fam A σ := by
    intro Fam hFam A σ hσ
    exact (OCRSProof.prune_subset f L _).trans
      (OCRSProof.characteristic_subset_greedy Fam A σ hσ ((hw.1 x).2.2 Fam hFam).1)
  constructor
  · intro hm ord hord
    apply hpr.trans
    unfold expOutput
    apply Finset.sum_le_sum
    intro Fam _
    by_cases hz : w x Fam = 0
    · simp [hz]
    · apply mul_le_mul_of_nonneg_left _ (hw0 Fam)
      apply OCRSProof.expect_mono x hx01
      intro A
      exact hm _ _ (hcontain Fam hz A (ord Fam A) (hord Fam A))
  · intro ord hord
    have hthin : ∀ Fam, w x Fam ≠ 0 → ∀ A,
        f (OCRSProof.prune f L (OCRSProof.characteristic Fam A)) / 4 ≤
          OCRSProof.expect (fun _ => (1/2:ℝ)) (fun C => f (greedyRun Fam A (ord Fam A C) ∩ C)) := by
      intro Fam hFam A
      apply OCRSProof.Thinning.almighty_thinning f hf0 hf
      intro C
      exact hcontain Fam hFam A (ord Fam A C) (hord Fam A C)
    have hbound : (1/4:ℝ) * (∑ Fam, w x Fam * OCRSProof.expect x
          (fun A => f (OCRSProof.prune f L (OCRSProof.characteristic Fam A)))) ≤
        expOutputHalf w x ord f := by
      unfold expOutputHalf
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro Fam _
      by_cases hz : w x Fam = 0
      · simp [hz]
      · rw [mul_left_comm]
        apply mul_le_mul_of_nonneg_left _ (hw0 Fam)
        rw [← OCRSProof.expect_mul]
        apply OCRSProof.expect_mono x hx01
        intro A
        simpa [OCRSProof.expect,div_eq_mul_inv,mul_comm] using hthin Fam hz A
    have h := (mul_le_mul_of_nonneg_left hpr (by norm_num : (0:ℝ) ≤ 1/4)).trans hbound
    nlinarith

end OnlineCRS.Submod

open OnlineCRS.Submod

theorem solution {α : Type} [Fintype α] [DecidableEq α]
    (𝓕 : Finset α → Prop) (P : Set (α → ℝ))
    (hPoly : IsPolytope P) (hRel : IsRelaxation 𝓕 P)
    (b c : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (w : (α → ℝ) → Finset (Finset α) → ℝ) (hw : OnlineCRS.Matroid.IsSelectableRand 𝓕 P b c w)
    (x : α → ℝ) (hx : x ∈ b • P)
    (f : Finset α → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f) :
    ((∀ A B : Finset α, A ⊆ B → f A ≤ f B) →
        ∀ ord : Finset (Finset α) → Finset α → List α, (∀ Fam A, IsOrder (ord Fam A)) →
          c * NonmonotoneSubmod.Shared.F f x ≤ expOutput w x ord f) ∧
      (∀ ord : Finset (Finset α) → Finset α → Finset α → List α,
        (∀ Fam A C, IsOrder (ord Fam A C)) →
          c / 4 * NonmonotoneSubmod.Shared.F f x ≤ expOutputHalf w x ord f) := by
  exact OnlineCRS.Submod.selectability_to_approximation 𝓕 P hPoly hRel b c hb0 hb1 hc0 hc1 w hw x hx f hf0 hf
