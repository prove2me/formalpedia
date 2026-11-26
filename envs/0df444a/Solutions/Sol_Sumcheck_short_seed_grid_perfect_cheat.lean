-- Prove2me | solution 1 for Sumcheck.short_seed_grid_perfect_cheat
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:46:54.515451+00:00
-- url     : https://prove2.me/submissions/4b0f9c41-b5aa-4319-a767-b987a53ed3cb

import Mathlib
open Polynomial
open scoped BigOperators

namespace PvsNP.SumcheckSeedBarrier

open Polynomial

variable {F : Type} [Field F]
variable {Seed A : Type}

/-- Each distinct history identifies the precise subset of seeds still
compatible with the public challenges. -/
noncomputable def fiber (seeds : Finset Seed) (step : Seed → A) (a : A) : Finset Seed := by
  classical
  exact seeds.filter (fun s => step s = a)

def history (challenge : Seed → ℕ → A) (s : Seed) (i : ℕ) : Fin i → A :=
  fun j => challenge s j.val

noncomputable def supporting (seeds : Finset Seed) (challenge : Seed → ℕ → A) (i : ℕ)
    (h : Fin i → A) : Finset Seed :=
  fiber seeds (fun s => history challenge s i) h

theorem support_step (seeds : Finset Seed) (challenge : Seed → ℕ → A)
    (s : Seed) (i : ℕ) : supporting seeds challenge (i+1) (history challenge s (i+1)) =
      fiber (supporting seeds challenge i (history challenge s i)) (fun z => challenge z i)
        (challenge s i) := by
  classical
  ext x
  simp only [supporting,fiber,Finset.mem_filter]
  constructor
  · rintro ⟨hx,e⟩
    refine ⟨⟨hx,?_⟩,?_⟩
    · funext j
      exact congrFun e ⟨j.val,by omega⟩
    · exact congrFun e ⟨i,by omega⟩
  · rintro ⟨⟨hx,e⟩,last⟩
    refine ⟨hx,?_⟩
    funext j
    by_cases h : j.val < i
    · exact congrFun e ⟨j.val,h⟩
    · have hj : j.val = i := by have := j.isLt; omega
      simpa only [history,hj] using last

def claims (challenge : Seed → ℕ → F)
    (prover : ∀ i : ℕ, (Fin i → F) → F → Polynomial F) (initial : F) (s : Seed) : ℕ → F
  | 0 => initial
  | i+1 => (prover i (history challenge s i) (claims challenge prover initial s i)).eval (challenge s i)

end PvsNP.SumcheckSeedBarrier

namespace PvsNP.SumcheckSeedBarrier

open Polynomial
open scoped BigOperators

variable {F : Type} [Field F]

/-- For a high-radix grid, any list of fewer than |H| guesses can be
satisfied simultaneously by a bounded-degree correction. -/
theorem exists_grid_correction (H G : Finset F) (smaller : G.card < H.card) (δ : F) :
    ∃ p : Polynomial F,
      p.natDegree ≤ 2*(H.card-1) ∧
      (∑ x ∈ H, p.eval x) = δ ∧ (∀ x ∈ G, p.eval x = 0) ∧ (δ=0 → p=0) := by
  classical
  obtain ⟨a,ha,haG⟩ := Finset.exists_mem_notMem_of_card_lt_card smaller
  let roots := G ∪ H.erase a
  let b : Polynomial F := ∏ u ∈ roots, (X-C u)
  have no : a ∉ roots := by simp [roots,haG]
  have evalB (x : F) : b.eval x = ∏ u ∈ roots, (x-u) := by
    simp [b,eval_prod]
  have zeroAt (x : F) (hx : x ∈ roots) : b.eval x = 0 := by
    rw [evalB]
    apply Finset.prod_eq_zero hx
    simp
  have nonzero : b.eval a ≠ 0 := by
    rw [evalB]
    exact Finset.prod_ne_zero_iff.2 fun u hu => sub_ne_zero.mpr (fun e => no (e ▸ hu))
  let p := C (δ/(b.eval a))*b
  have evalP (x : F) : p.eval x = (δ/(b.eval a))*(b.eval x) := by simp [p]
  refine ⟨p,?_,?_,?_,?_⟩
  · have bc : b.natDegree ≤ roots.card := by
      apply (natDegree_prod_le ..).trans
      simp only [natDegree_X_sub_C, Finset.sum_const, nsmul_eq_mul,mul_one]
      exact le_rfl
    refine (natDegree_C_mul_le _ _).trans (bc.trans ?_)
    have bound := Finset.card_union_le G (H.erase a)
    rw [Finset.card_erase_of_mem ha] at bound
    change roots.card ≤ G.card + (H.card-1) at bound
    omega
  · calc
      _ = p.eval a := by
        apply Finset.sum_eq_single a
        · intro x hx hxne
          have hr : x ∈ roots := Finset.mem_union_right G (Finset.mem_erase.mpr ⟨hxne,hx⟩)
          rw [evalP,zeroAt x hr,mul_zero]
        · exact fun bad => (bad ha).elim
      _ = δ := by rw [evalP,div_mul_cancel₀ _ nonzero]
  · intro x hx
    rw [evalP, zeroAt x (Finset.mem_union_left _ hx),mul_zero]
  · intro e
    simp [p,e]

section Shortlist

variable {Seed A : Type} [Fintype A]

private theorem choose_top (pool : Finset A) (score : A → ℕ) (k : ℕ) (room : k ≤ pool.card) :
    ∃ top : Finset A, top ⊆ pool ∧ top.card = k ∧
      ∀ a ∈ pool, a ∉ top → ∀ b ∈ top, score a ≤ score b := by
  classical
  induction k generalizing pool with
  | zero => exact ⟨∅,Finset.empty_subset _,rfl,by simp⟩
  | succ k ih =>
    have hn : pool.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨c,hc,high⟩ := Finset.exists_max_image pool score hn
    obtain ⟨top,ht,card,ordered⟩ := ih (pool.erase c) (by rw [Finset.card_erase_of_mem hc]; omega)
    have notTop : c ∉ top := fun hc' => Finset.notMem_erase c pool (ht hc')
    refine ⟨insert c top, ?_, by rw [Finset.card_insert_of_notMem notTop,card], ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with e | mem
      · rwa [e]
      · exact Finset.mem_of_mem_erase (ht mem)
    · intro a ha miss b hb
      rcases Finset.mem_insert.mp hb with e | mem
      · rw [e]
        exact high a ha
      · have ane : a ≠ c := fun e => miss (Finset.mem_insert.mpr (Or.inl e))
        exact ordered a (Finset.mem_erase.mpr ⟨ane,ha⟩)
          (fun h => miss (Finset.mem_insert_of_mem h)) b mem

/-- The top k challenge fibers by number of supporting seeds. -/
noncomputable def shortlist (seeds : Finset Seed) (step : Seed → A) (k : ℕ)
    (fit : k ≤ Fintype.card A) : Finset A := by
  classical
  exact Classical.choose (choose_top (Finset.univ : Finset A) (fun a => (fiber seeds step a).card) k
    (by simpa using fit))

private theorem shortlist_spec (seeds : Finset Seed) (step : Seed → A) (k : ℕ)
    (fit : k ≤ Fintype.card A) : (shortlist seeds step k fit).card = k ∧
    ∀ a ∉ shortlist seeds step k fit, ∀ b ∈ shortlist seeds step k fit,
      (fiber seeds step a).card ≤ (fiber seeds step b).card := by
  classical
  have h := Classical.choose_spec (choose_top (Finset.univ : Finset A)
    (fun a => (fiber seeds step a).card) k (by simpa using fit))
  exact ⟨h.2.1,fun a ha b hb => h.2.2 a (Finset.mem_univ _) ha b hb⟩

/-- A seed whose next challenge misses all k predictions now lies in a
fiber no greater than each of k+1 distinct challenge fibers. -/
theorem missed_shortlist_contracts (seeds : Finset Seed) (step : Seed → A) (k : ℕ)
    (fit : k ≤ Fintype.card A) (a : A) (miss : a ∉ shortlist seeds step k fit) :
    (k+1)*(fiber seeds step a).card ≤ seeds.card := by
  classical
  let top := shortlist seeds step k fit
  let picked := insert a top
  obtain ⟨size,h⟩ := shortlist_spec seeds step k fit
  have proper : (picked.biUnion (fiber seeds step)) ⊆ seeds := by
    intro s hs
    obtain ⟨b,_,hb⟩ := Finset.mem_biUnion.mp hs
    simp only [fiber,Finset.mem_filter] at hb
    exact hb.1
  have disj : (picked : Set A).PairwiseDisjoint (fiber seeds step) := by
    intro b hb c hc ne
    apply Finset.disjoint_left.2
    intro s h₁ h₂
    simp only [fiber,Finset.mem_filter] at h₁ h₂
    exact ne (h₁.2.symm.trans h₂.2)
  have count := Finset.card_le_card proper
  rw [Finset.card_biUnion disj] at count
  have pickCard : picked.card = k+1 := by rw [show picked = insert a top from rfl,Finset.card_insert_of_notMem miss,size]
  have sorted (b : A) (hb : b ∈ picked) : (fiber seeds step a).card ≤ (fiber seeds step b).card := by
    rcases Finset.mem_insert.mp hb with e | m
    · rw [e]
    · exact h a miss b m
  have min := Finset.sum_le_sum sorted
  rw [Finset.sum_const_nat (fun _ _ => rfl),pickCard] at min
  exact min.trans count

end Shortlist

section GridProtocol

variable {Seed : Type} [Fintype F]

/-- Number of Boolean assignments replaced by the mixed-radix grid. -/
def gridVolume (H : ℕ → Finset F) : ℕ → ℕ
  | 0 => 1
  | m+1 => gridVolume H m * (H m).card

private theorem grid_size_le_field (H : Finset F) : H.card-1 ≤ Fintype.card F := by
  classical
  exact (Nat.sub_le ..).trans (Finset.card_le_univ H)

noncomputable def gridPredict (seeds : Finset Seed) (draw : Seed → ℕ → F)
    (H : ℕ → Finset F) (i : ℕ) (h : Fin i → F) : Finset F :=
  shortlist (supporting seeds draw i h) (fun s => draw s i) ((H i).card-1) (grid_size_le_field _)

private theorem predict_card (seeds : Finset Seed) (draw : Seed → ℕ → F)
    (H : ℕ → Finset F) (i : ℕ) (h : Fin i → F) :
    (gridPredict seeds draw H i h).card = (H i).card-1 :=
  (shortlist_spec _ _ _ _).1

/-- With fewer seeds than the grid volume, the prover's short list
contains some actual next challenge on every seed. -/
theorem grid_predict_some_round (seeds : Finset Seed) (draw : Seed → ℕ → F)
    (H : ℕ → Finset F) (nonempty : ∀ i, (H i).Nonempty)
    (m : ℕ) (short : seeds.card < gridVolume H m) (s : Seed) (hs : s ∈ seeds) :
    ∃ i < m, draw s i ∈ gridPredict seeds draw H i (history draw s i) := by
  classical
  by_contra! miss
  have bound (i : ℕ) (hi : i ≤ m) : gridVolume H i *
      (supporting seeds draw i (history draw s i)).card ≤ seeds.card := by
    induction i with
    | zero =>
      simp only [gridVolume,one_mul]
      apply Finset.card_le_card
      intro z hz
      simp only [supporting,fiber,Finset.mem_filter] at hz
      exact hz.1
    | succ i ih =>
      have someSeed := missed_shortlist_contracts (supporting seeds draw i (history draw s i))
        (fun z => draw z i) ((H i).card-1) (grid_size_le_field _) (draw s i) (miss i (by omega))
      have hpos := Finset.card_pos.mpr (nonempty i)
      rw [Nat.sub_add_cancel hpos] at someSeed
      rw [gridVolume,support_step,mul_assoc]
      exact (Nat.mul_le_mul_left _ someSeed).trans (ih (by omega))
  have spot : s ∈ supporting seeds draw m (history draw s m) := by simp [supporting,fiber,hs]
  have sz := Finset.card_pos.mpr (show (supporting seeds draw m (history draw s m)).Nonempty from ⟨s,spot⟩)
  exact (Nat.not_lt_of_ge ((Nat.le_mul_of_pos_right _ sz).trans (bound m le_rfl))) short

private theorem guess_smaller (seeds : Finset Seed) (draw : Seed → ℕ → F)
    (H : ℕ → Finset F) (nonempty : ∀ i, (H i).Nonempty) (i : ℕ) (h : Fin i → F) :
    (gridPredict seeds draw H i h).card < (H i).card := by
  rw [predict_card]
  have := Finset.card_pos.mpr (nonempty i)
  omega

/-- The ordinary sum-check transition still accepts an arbitrary claimed
sum on every seed, even after grouping Boolean address bits into digits. -/
theorem short_seed_grid_sumcheck_perfect_cheat
    (seeds : Finset Seed) (draw : Seed → ℕ → F) (m : ℕ)
    (H : ℕ → Finset F) (nonempty : ∀ i, (H i).Nonempty) (short : seeds.card < gridVolume H m)
    (degree : ℕ → ℕ) (degreeFit : ∀ i, 2*((H i).card-1) ≤ degree i)
    (truth : ∀ i : ℕ, (Fin i → F) → F)
    (honest : ∀ i : ℕ, (Fin i → F) → Polynomial F)
    (honestDegree : ∀ i h, (honest i h).natDegree ≤ degree i)
    (honestSum : ∀ i h, (∑ x ∈ H i, (honest i h).eval x) = truth i h)
    (honestPoint : ∀ s i, (honest i (history draw s i)).eval (draw s i) =
      truth (i+1) (history draw s (i+1)))
    (initial : F) :
    ∃ prover : ∀ i : ℕ, (Fin i → F) → F → Polynomial F,
      (∀ i h v, (prover i h v).natDegree ≤ degree i) ∧
      (∀ i h v, (∑ x ∈ H i, (prover i h v).eval x) = v) ∧
      (∀ s ∈ seeds, claims draw prover initial s m = truth m (history draw s m)) := by
  classical
  let choose (i : ℕ) (h : Fin i → F) (δ : F) :=
    Classical.choose (exists_grid_correction (H i) (gridPredict seeds draw H i h)
      (guess_smaller seeds draw H nonempty i h) δ)
  have prop (i : ℕ) (h : Fin i → F) (δ : F) :=
    Classical.choose_spec (exists_grid_correction (H i) (gridPredict seeds draw H i h)
      (guess_smaller seeds draw H nonempty i h) δ)
  let prover (i : ℕ) (h : Fin i → F) (claim : F) := honest i h + choose i h (claim-truth i h)
  refine ⟨prover,?_,?_,?_⟩
  · intro i h v
    exact (natDegree_add_le ..).trans (max_le (honestDegree i h)
      (((prop i h (v-truth i h)).1).trans (degreeFit i)))
  · intro i h v
    simp only [prover,eval_add,Finset.sum_add_distrib,honestSum]
    have outcome : (∑ x ∈ H i, (choose i h (v-truth i h)).eval x) = v-truth i h :=
      (prop i h (v-truth i h)).2.1
    rw [outcome]
    ring
  · intro s hs
    obtain ⟨i,hi,hit⟩ := grid_predict_some_round seeds draw H nonempty m short s hs
    let real (j : ℕ) := truth j (history draw s j)
    let run (j : ℕ) := claims draw prover initial s j
    have aligned : run (i+1) = real (i+1) := by
      change (prover i (history draw s i) (run i)).eval (draw s i) = _
      have z : (choose i (history draw s i) (run i-real i)).eval (draw s i) = 0 :=
        (prop i (history draw s i) (run i-real i)).2.2.1 _ hit
      simp only [prover,eval_add,show real i = truth i (history draw s i) from rfl] at z ⊢
      rw [z,add_zero]
      exact honestPoint s i
    have stable (j : ℕ) (same : run j = real j) : run (j+1) = real (j+1) := by
      change (prover j (history draw s j) (run j)).eval (draw s j) = _
      have z : choose j (history draw s j) 0 = 0 := (prop j (history draw s j) 0).2.2.2 rfl
      rw [same]
      simp only [prover,real,sub_self,z,add_zero]
      exact honestPoint s j
    have keeps (j : ℕ) (ij : i+1 ≤ j) : run j = real j := by
      induction j, ij using Nat.le_induction with
      | base => exact aligned
      | succ j _ ih => exact stable j ih
    exact keeps m (by omega)

end GridProtocol

end PvsNP.SumcheckSeedBarrier

theorem solution {F Seed : Type} [Field F] [Fintype F]
    (seeds : Finset Seed) (draw : Seed → ℕ → F) (m : ℕ)
    (H : ℕ → Finset F) (nonempty : ∀ i, (H i).Nonempty) (short : seeds.card < ∏ i ∈ Finset.range m, (H i).card)
    (degree : ℕ → ℕ) (degreeFit : ∀ i, 2*((H i).card-1) ≤ degree i)
    (truth : ∀ i : ℕ, (Fin i → F) → F)
    (honest : ∀ i : ℕ, (Fin i → F) → Polynomial F)
    (honestDegree : ∀ i h, (honest i h).natDegree ≤ degree i)
    (honestSum : ∀ i h, (∑ x ∈ H i, (honest i h).eval x) = truth i h)
    (honestPoint : ∀ s i, (honest i (fun j : Fin i => draw s j.val)).eval (draw s i) =
      truth (i+1) (fun j : Fin (i+1) => draw s j.val))
    (initial : F) :
    ∃ prover : ∀ i : ℕ, (Fin i → F) → F → Polynomial F,
      (∀ i h v, (prover i h v).natDegree ≤ degree i) ∧
      (∀ i h v, (∑ x ∈ H i, (prover i h v).eval x) = v) ∧
      (∀ s ∈ seeds, ∀ run : ℕ → F, run 0 = initial →
        (∀ i, run (i+1) = (prover i (fun j : Fin i => draw s j.val) (run i)).eval (draw s i)) →
        run m = truth m (fun j : Fin m => draw s j.val)) := by
  have vol (k : ℕ) : PvsNP.SumcheckSeedBarrier.gridVolume H k = ∏ i ∈ Finset.range k, (H i).card := by
    induction k with
    | zero => simp [PvsNP.SumcheckSeedBarrier.gridVolume]
    | succ k ih => rw [PvsNP.SumcheckSeedBarrier.gridVolume, Finset.prod_range_succ, ih]
  obtain ⟨prover, hd, hs, hf⟩ := PvsNP.SumcheckSeedBarrier.short_seed_grid_sumcheck_perfect_cheat
    seeds draw m H nonempty (by rwa [vol]) degree degreeFit truth honest honestDegree honestSum honestPoint initial
  refine ⟨prover, hd, hs, ?_⟩
  intro s hseed run h0 step
  have eqrun (i : ℕ) : run i = PvsNP.SumcheckSeedBarrier.claims draw prover initial s i := by
    induction i with
    | zero => exact h0
    | succ i ih => rw [step, ih]; rfl
  rw [eqrun m]
  exact hf s hseed
