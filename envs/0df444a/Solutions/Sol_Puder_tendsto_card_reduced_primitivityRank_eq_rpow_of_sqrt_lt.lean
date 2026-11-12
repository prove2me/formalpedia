-- Prove2me | solution 1 for Puder.tendsto_card_reduced_primitivityRank_eq_rpow_of_sqrt_lt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T20:34:05.023756+00:00
-- url     : https://prove2.me/submissions/ba6e9fa2-6a8a-4a16-8648-6a1ddee05d24

import Mathlib
import Definitions.Def_StrongConv
import Definitions.Def_StrongConvPuder
import Theorems.Thm_Puder_limsup_sum_ncard_crit_reduced_rpow_le
import Theorems.Thm_Puder_isAlgExt_zpowers_of_mem_crit
import Theorems.Thm_Puder_setOf_isAlgExt_finite_of_fg

namespace Puder.Q284Fin

/-- `Crit(w)` is finite: critical subgroups are algebraic extensions of `⟨w⟩` (Claim 3.1), of which there are
finitely many (Takahasi). -/
theorem crit_finite {d : ℕ} (w : FreeGroup (Fin d)) : (Puder.Crit w).Finite :=
  (Puder.setOf_isAlgExt_finite_of_fg (Subgroup.zpowers w)
      ⟨{w}, by rw [Finset.coe_singleton, ← Subgroup.zpowers_eq_closure]⟩).subset
    fun _ hJ => Puder.isAlgExt_zpowers_of_mem_crit hJ

end Puder.Q284Fin


section
open Filter Topology
namespace Puder.Q284T82
/-! q263 T8.2: Puder Theorem 8.2 (reduced words of primitivity rank `m`, case `2m - 1 > √(2k-1)`),
from Proposition 4.3, Theorem 2.3 (finiteness of `Crit`) and the growth of primitive reduced
words (Puder p. 37). Word/letter helpers copied from `Q263T85L`. -/
/-- The endpoint of the walk spelled by a letter sequence. -/
noncomputable def word {k t : ℕ} (i : Fin t → Fin k ⊕ Fin k) : FreeGroup (Fin k) :=
  StrongConv.wordFree (List.ofFn fun j => some (i j))

/-- Non-backtracking. -/
def NB {k t : ℕ} (i : Fin t → Fin k ⊕ Fin k) : Prop :=
  ∀ (j : Fin t) (hj : (j : ℕ) + 1 < t), i ⟨j + 1, hj⟩ ≠ (i j).swap

theorem crit_nonempty {k : ℕ} (w : FreeGroup (Fin k)) (m : ℕ) (h : primitivityRank w = m) :
    (Crit w).Nonempty := by
  classical
  have hex : ∃ r : ℕ, ∃ J : Subgroup (FreeGroup (Fin k)), w ∈ J ∧ HasRank J r ∧
      ¬ IsPrimitiveIn J w := by
    by_contra hne
    push Not at hne
    have htop : primitivityRank w = ⊤ := by
      unfold primitivityRank
      simp only [iInf_eq_top]
      intro r hr
      obtain ⟨J, h1, h2, h3⟩ := hr
      exact absurd h3 (not_not.mpr (hne r J h1 h2))
    rw [htop] at h
    exact ENat.top_ne_natCast m h
  have hval : primitivityRank w = (Nat.find hex : ℕ∞) := by
    unfold primitivityRank
    apply le_antisymm
    · exact iInf₂_le (Nat.find hex) (Nat.find_spec hex)
    · exact le_iInf₂ fun r hr => by exact_mod_cast Nat.find_min' hex hr
  obtain ⟨J, hw, hr, hnp⟩ := Nat.find_spec hex
  exact ⟨J, hw, hnp, Nat.find hex, hr, hval.symm⟩

/-! ## Non-backtracking sequences are the reduced ones -/
/-- The generator a letter stands for. -/
def gen {k : ℕ} : Fin k ⊕ Fin k → FreeGroup (Fin k)
  | Sum.inl x => FreeGroup.of x
  | Sum.inr x => (FreeGroup.of x)⁻¹

/-- The letter as a generator-with-sign pair. -/
def toP {k : ℕ} : Fin k ⊕ Fin k → Fin k × Bool
  | Sum.inl x => (x, true)
  | Sum.inr x => (x, false)

theorem word_eq {k t : ℕ} (i : Fin t → Fin k ⊕ Fin k) :
    word i = (List.ofFn fun j => gen (i j)).prod := by
  unfold word StrongConv.wordFree
  rw [List.map_ofFn]
  congr 2
  funext j
  simp only [Function.comp]
  rcases i j with x | x <;> rfl

theorem gen_eq_mk {k : ℕ} (a : Fin k ⊕ Fin k) : gen a = FreeGroup.mk [toP a] := by
  rcases a with x | x
  · rfl
  · simp [gen, toP, FreeGroup.of, FreeGroup.inv_mk, FreeGroup.invRev]

theorem prod_map_gen {k : ℕ} (l : List (Fin k ⊕ Fin k)) :
    (l.map gen).prod = FreeGroup.mk (l.map toP) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, ih, gen_eq_mk, FreeGroup.mul_mk]
    rfl

theorem word_eq_mk {k t : ℕ} (i : Fin t → Fin k ⊕ Fin k) :
    word i = FreeGroup.mk (List.ofFn fun j => toP (i j)) := by
  rw [word_eq]
  have h1 : (List.ofFn fun j => gen (i j)) = (List.ofFn i).map gen := by
    rw [List.map_ofFn]; rfl
  have h2 : (List.ofFn fun j => toP (i j)) = (List.ofFn i).map toP := by
    rw [List.map_ofFn]; rfl
  rw [h1, h2, prod_map_gen]

theorem toP_rel {k : ℕ} (a b : Fin k ⊕ Fin k) :
    ((toP a).1 = (toP b).1 → (toP a).2 = (toP b).2) ↔ b ≠ a.swap := by
  rcases a with x | x <;> rcases b with y | y <;> simp [toP, eq_comm]

theorem NB_iff_isReduced {k t : ℕ} (i : Fin t → Fin k ⊕ Fin k) :
    NB i ↔ FreeGroup.IsReduced (List.ofFn fun j => toP (i j)) := by
  rw [NB, FreeGroup.IsReduced, List.isChain_ofFn]
  simp only [toP_rel]
  constructor
  · intro H j hj
    exact H ⟨j, by omega⟩ hj
  · intro H j hj
    exact H j hj

theorem NB_iff_length {k t : ℕ} (i : Fin t → Fin k ⊕ Fin k) :
    NB i ↔ (word i).toWord.length = t := by
  rw [NB_iff_isReduced, word_eq_mk, FreeGroup.toWord_mk]
  set M := List.ofFn fun j => toP (i j)
  have hM : M.length = t := by simp [M]
  constructor
  · intro hr
    rw [hr.reduce_eq, hM]
  · intro hl
    by_contra hr
    rw [FreeGroup.isReduced_iff_not_step] at hr
    push Not at hr
    obtain ⟨L₂, hs⟩ := hr
    have e := FreeGroup.reduce.Step.eq hs
    have hle := FreeGroup.Red.length_le (FreeGroup.reduce.red (L := L₂))
    have hst := hs.length
    rw [e] at hl
    omega

/-! ## Counting non-backtracking sequences -/
theorem sum_snoc {k r : ℕ} (f : (Fin (r + 1) → Fin k ⊕ Fin k) → ℝ) :
    ∑ j, f j = ∑ i : Fin r → Fin k ⊕ Fin k, ∑ a, f (Fin.snoc i a) := by
  rw [← (Fin.snocEquiv fun _ => Fin k ⊕ Fin k).sum_comp, Fintype.sum_prod_type_right]
  rfl

theorem NB_snoc_succ {k r : ℕ} (i : Fin (r + 1) → Fin k ⊕ Fin k) (a : Fin k ⊕ Fin k) :
    NB (Fin.snoc i a : Fin (r + 2) → Fin k ⊕ Fin k) ↔ NB i ∧ a ≠ (i (Fin.last r)).swap := by
  simp only [NB]
  constructor
  · intro H
    refine ⟨fun j hj => ?_, ?_⟩
    · have := H ⟨j, by omega⟩ (by simp; omega)
      simpa [Fin.snoc, hj, j.isLt] using this
    · have := H ⟨r, by omega⟩ (by simp)
      simpa [Fin.snoc, Fin.last] using this
  · rintro ⟨H, ha⟩ j hj
    have hj' : (j : ℕ) < r + 1 := by simp at hj; omega
    by_cases h2 : (j : ℕ) + 1 < r + 1
    · have := H ⟨j, hj'⟩ h2
      simp [Fin.snoc, h2, hj']
      exact this
    · have hjr : (j : ℕ) = r := by omega
      simp [Fin.snoc, hjr]
      convert ha using 4
      ext
      simp [hjr]

instance {k t : ℕ} : DecidablePred (@NB k t) := fun i => by unfold NB; infer_instance

/-- The number of non-backtracking sequences of length `t` in `F_m`. -/
noncomputable def N (m t : ℕ) : ℝ :=
  ((Finset.univ.filter fun i : Fin t → Fin m ⊕ Fin m => NB i).card : ℝ)

theorem N_eq_sum (m t : ℕ) : N m t = ∑ i : Fin t → Fin m ⊕ Fin m, if NB i then 1 else 0 := by
  classical
  unfold N
  rw [Finset.sum_boole]

theorem card_ne_swap {m : ℕ} (x : Fin m ⊕ Fin m) :
    (2 * m : ℝ) - 1 ≤ ∑ a : Fin m ⊕ Fin m, if a ≠ x then (1 : ℝ) else 0 := by
  classical
  rw [Finset.sum_boole]
  have : (Finset.univ.filter fun a : Fin m ⊕ Fin m => a ≠ x) = Finset.univ.erase x := by
    ext a; simp
  rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_sum,
    Fintype.card_fin]
  have h1 : 1 ≤ m + m := by
    rcases x with x | x <;> have := x.isLt <;> omega
  push_cast [Nat.cast_sub h1]
  linarith

theorem N_one (m : ℕ) : N m 1 = 2 * m := by
  classical
  unfold N
  have : (Finset.univ.filter fun i : Fin 1 → Fin m ⊕ Fin m => NB i) = Finset.univ := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    intro j hj; omega
  rw [this, Finset.card_univ, Fintype.card_fun, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_fin]
  push_cast; ring

theorem N_succ (m r : ℕ) : (2 * m - 1 : ℝ) * N m (r + 1) ≤ N m (r + 2) := by
  classical
  rw [N_eq_sum m (r + 1), N_eq_sum m (r + 2),
    sum_snoc (fun j : Fin (r + 2) → Fin m ⊕ Fin m => if NB j then (1 : ℝ) else 0), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  simp only [NB_snoc_succ]
  by_cases hi : NB i
  · simp only [hi, true_and, if_true, mul_one]
    exact card_ne_swap _
  · simp [hi]

theorem pow_le_N (m : ℕ) (hm : 1 ≤ m) : ∀ t : ℕ, (2 * m - 1 : ℝ) ^ t ≤ N m t
  | 0 => by
    classical
    unfold N
    have : (Finset.univ.filter fun i : Fin 0 → Fin m ⊕ Fin m => NB i) = Finset.univ := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      intro j; exact j.elim0
    rw [this]; simp
  | 1 => by rw [N_one]; simp
  | r + 2 => by
    have h1 := pow_le_N m hm (r + 1)
    have hq : (0 : ℝ) ≤ 2 * m - 1 := by
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    calc (2 * m - 1 : ℝ) ^ (r + 2) = (2 * m - 1) * (2 * m - 1) ^ (r + 1) := by ring
      _ ≤ (2 * m - 1) * N m (r + 1) := mul_le_mul_of_nonneg_left h1 hq
      _ ≤ N m (r + 2) := N_succ m r

/-! ## Transfer from `F_m` to `F_k` -/
/-- The letter map induced by `Fin.castLE`. -/
def lift {m k : ℕ} (hm : m ≤ k) : Fin m ⊕ Fin m → Fin k ⊕ Fin k :=
  Sum.map (Fin.castLE hm) (Fin.castLE hm)

theorem lift_injective {m k : ℕ} (hm : m ≤ k) : Function.Injective (lift hm) :=
  Sum.map_injective.2 ⟨Fin.castLE_injective hm, Fin.castLE_injective hm⟩

theorem lift_swap {m k : ℕ} (hm : m ≤ k) (a : Fin m ⊕ Fin m) :
    lift hm a.swap = (lift hm a).swap := by
  rcases a with x | x <;> rfl

theorem NB_lift_iff {m k t : ℕ} (hm : m ≤ k) (i : Fin t → Fin m ⊕ Fin m) :
    NB (lift hm ∘ i) ↔ NB i := by
  simp only [NB, Function.comp, ← lift_swap, (lift_injective hm).ne_iff]

theorem gen_lift {m k : ℕ} (hm : m ≤ k) (a : Fin m ⊕ Fin m) :
    gen (lift hm a) = FreeGroup.map (Fin.castLE hm) (gen a) := by
  rcases a with x | x <;> simp [gen, lift]

theorem word_lift {m k t : ℕ} (hm : m ≤ k) (i : Fin t → Fin m ⊕ Fin m) :
    word (lift hm ∘ i) = FreeGroup.map (Fin.castLE hm) (word i) := by
  rw [word_eq, word_eq, map_list_prod, List.map_ofFn]
  congr 2
  funext j
  simp [gen_lift]

/-- `F_m` is isomorphic to its image in `F_k`. -/
noncomputable def emb {m k : ℕ} (hm : m ≤ k) :
    FreeGroup (Fin m) ≃* (FreeGroup.map (Fin.castLE hm)).range :=
  MonoidHom.ofInjective (FreeGroup.map_injective (Fin.castLE_injective hm))

theorem hasRank_range {m k : ℕ} (hm : m ≤ k) :
    HasRank (FreeGroup.map (Fin.castLE hm)).range m :=
  ⟨(FreeGroupBasis.ofFreeGroup (Fin m)).map (emb hm)⟩

theorem isPrimitiveIn_top_of_range {m k : ℕ} (hm : m ≤ k) (w : FreeGroup (Fin m))
    (h : IsPrimitiveIn (FreeGroup.map (Fin.castLE hm)).range (FreeGroup.map (Fin.castLE hm) w)) :
    IsPrimitiveIn ⊤ w := by
  obtain ⟨ι, b, j, hb⟩ := h
  refine ⟨ι, b.map ((emb hm).symm.trans Subgroup.topEquiv.symm), j, ?_⟩
  rw [FreeGroupBasis.map_apply]
  have : (emb hm) w = b j := Subtype.ext (by rw [hb]; rfl)
  simp [← this]

/-! ## The counting inequality -/
/-- The number of reduced sequences of length `t` in `F_k` with primitivity rank `m`. -/
noncomputable def c (k m t : ℕ) : ℝ :=
  ((Finset.univ.filter fun i : Fin t → Fin k ⊕ Fin k =>
      (word i).toWord.length = t ∧ primitivityRank (word i) = m).card : ℝ)

open Classical in
/-- The number of reduced sequences of length `t` in `F_m` primitive in `F_m`. -/
noncomputable def p (m t : ℕ) : ℝ :=
  ((Finset.univ.filter fun i : Fin t → Fin m ⊕ Fin m =>
      (word i).toWord.length = t ∧ IsPrimitiveIn ⊤ (word i)).card : ℝ)

theorem freeGroup_fin_zero_eq_one (g : FreeGroup (Fin 0)) : g = 1 := by
  induction g using FreeGroup.induction_on with
  | C1 => rfl
  | of i => exact i.elim0
  | inv_of i _ => exact i.elim0
  | mul x y hx hy => rw [hx, hy, mul_one]

theorem one_le_primitivityRank {k : ℕ} (w : FreeGroup (Fin k)) (hw1 : w ≠ 1) :
    1 ≤ primitivityRank w := by
  unfold primitivityRank
  refine le_iInf₂ fun r hr => ?_
  obtain ⟨J, hw, ⟨b⟩, _⟩ := hr
  rcases Nat.eq_zero_or_pos r with h0 | hpos
  · subst h0
    exfalso
    apply hw1
    have : (⟨w, hw⟩ : J) = 1 := by
      rw [← b.repr.symm_apply_apply ⟨w, hw⟩, freeGroup_fin_zero_eq_one (b.repr ⟨w, hw⟩)]
      exact map_one _
    exact congrArg Subtype.val this
  · exact_mod_cast hpos

theorem rank_of_not_prim {m k t : ℕ} (hm : m ≤ k) (ht : 1 ≤ t) (i : Fin t → Fin m ⊕ Fin m)
    (hi : NB i) (hp : ¬ IsPrimitiveIn ⊤ (word i)) :
    ∃ m' ∈ Finset.Icc 1 m, (word (lift hm ∘ i)).toWord.length = t ∧
      primitivityRank (word (lift hm ∘ i)) = m' := by
  have hlen : (word (lift hm ∘ i)).toWord.length = t := (NB_iff_length _).1 ((NB_lift_iff hm i).2 hi)
  have hne : word (lift hm ∘ i) ≠ 1 := by
    intro h1
    rw [h1, FreeGroup.toWord_one] at hlen
    simp at hlen
    omega
  have hle : primitivityRank (word (lift hm ∘ i)) ≤ m := by
    refine iInf₂_le m ⟨_, MonoidHom.mem_range.2 ⟨word i, (word_lift hm i).symm⟩,
      hasRank_range hm, fun h => hp ?_⟩
    rw [word_lift] at h
    exact isPrimitiveIn_top_of_range hm _ h
  have hge := one_le_primitivityRank _ hne
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (ENat.natCast_ne_top m) hle)
  rw [← hn] at hle hge
  refine ⟨n, Finset.mem_Icc.2 ⟨by exact_mod_cast hge, by exact_mod_cast hle⟩, hlen, hn.symm⟩

theorem N_le (k m t : ℕ) (hm : m ≤ k) (ht : 1 ≤ t) :
    N m t ≤ p m t + ∑ m' ∈ Finset.Icc 1 m, c k m' t := by
  classical
  unfold N p c
  set A := Finset.univ.filter fun i : Fin t → Fin m ⊕ Fin m => NB i
  rw [← Finset.card_filter_add_card_filter_not (s := A) (fun i => IsPrimitiveIn ⊤ (word i))]
  push_cast
  gcongr
  · intro i hi
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact ⟨(NB_iff_length i).1 hi.1, hi.2⟩
  · have h1 : (A.filter fun i => ¬ IsPrimitiveIn ⊤ (word i)).card ≤
        ((Finset.Icc 1 m).biUnion fun m' => Finset.univ.filter fun i : Fin t → Fin k ⊕ Fin k =>
          (word i).toWord.length = t ∧ primitivityRank (word i) = m').card := by
      apply Finset.card_le_card_of_injOn (fun i => lift hm ∘ i)
      · intro i hi
        simp only [A, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
          Set.mem_ofPred_eq] at hi
        obtain ⟨m', hm', h⟩ := rank_of_not_prim hm ht i hi.1 hi.2
        simp only [Finset.coe_biUnion, Finset.coe_filter, Set.mem_iUnion, Finset.mem_coe,
          Finset.mem_univ, true_and, Set.mem_ofPred_eq]
        exact ⟨m', hm', h⟩
      · intro a _ b _ hab
        exact (lift_injective hm).comp_left hab
    have h2 := Finset.card_biUnion_le (s := Finset.Icc 1 m) (t := fun m' =>
      Finset.univ.filter fun i : Fin t → Fin k ⊕ Fin k =>
          (word i).toWord.length = t ∧ primitivityRank (word i) = m')
    have h3 : (((A.filter fun i => ¬ IsPrimitiveIn ⊤ (word i)).card : ℕ) : ℝ) ≤
        ((∑ m' ∈ Finset.Icc 1 m, (Finset.univ.filter fun i : Fin t → Fin k ⊕ Fin k =>
          (word i).toWord.length = t ∧ primitivityRank (word i) = m').card : ℕ) : ℝ) := by
      exact_mod_cast h1.trans h2
    push_cast at h3
    convert h3

/-! ## Growth bounds -/
theorem c_nonneg (k m t : ℕ) : 0 ≤ c k m t := by unfold c; positivity

theorem c_bounds (k m : ℕ) (hk : 2 ≤ k) (hm1 : 1 ≤ m) (hm : m ≤ k) :
    IsBoundedUnder (· ≤ ·) atTop (fun t : ℕ => c k m t ^ (1 / (t : ℝ))) ∧
      limsup (fun t : ℕ => c k m t ^ (1 / (t : ℝ))) atTop ≤
        if (2 * m - 1 : ℝ) ≤ Real.sqrt (2 * k - 1) then Real.sqrt (2 * k - 1) else 2 * m - 1 := by
  obtain ⟨hB, hL⟩ := Puder.limsup_sum_ncard_crit_reduced_rpow_le k m hk hm1 hm
  have hle : ∀ t : ℕ, c k m t ^ (1 / (t : ℝ)) ≤
      (∑ i : Fin t → Fin k ⊕ Fin k with
            (StrongConv.wordFree (List.ofFn fun j => some (i j))).toWord.length = t ∧
              primitivityRank (StrongConv.wordFree (List.ofFn fun j => some (i j))) = m,
          ((Crit (StrongConv.wordFree (List.ofFn fun j => some (i j)))).ncard : ℝ)) ^
          (1 / (t : ℝ)) := by
    intro t
    apply Real.rpow_le_rpow (c_nonneg k m t) _ (by positivity)
    unfold c word
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_filter] at hi
    have hne := crit_nonempty _ m hi.2.2
    have := (Set.ncard_pos (Puder.Q284Fin.crit_finite _)).2 hne
    simp only [Nat.cast_one]
    exact_mod_cast this
  have hB' : IsBoundedUnder (· ≤ ·) atTop (fun t : ℕ => c k m t ^ (1 / (t : ℝ))) :=
    hB.mono_le (Eventually.of_forall hle)
  refine ⟨hB', le_trans (limsup_le_limsup (Eventually.of_forall hle) ?_ hB) hL⟩
  exact isCoboundedUnder_le_of_le atTop (fun t => Real.rpow_nonneg (c_nonneg k m t) _)

theorem eventually_le_pow {f : ℕ → ℝ} (hf : ∀ t, 0 ≤ f t) {a : ℝ}
    (h : ∀ᶠ t : ℕ in atTop, f t ^ (1 / (t : ℝ)) < a) : ∀ᶠ t : ℕ in atTop, f t ≤ a ^ t := by
  filter_upwards [h, eventually_ge_atTop 1] with t h1 ht
  have hpow : (f t ^ (1 / (t : ℝ))) ^ t ≤ a ^ t :=
    pow_le_pow_left₀ (Real.rpow_nonneg (hf t) _) h1.le t
  rwa [one_div, Real.rpow_inv_natCast_pow (hf t) (by omega)] at hpow

theorem c_eventually_le (k m : ℕ) (hk : 2 ≤ k) (hm1 : 1 ≤ m) (hm : m ≤ k) (a : ℝ)
    (ha : Real.sqrt (2 * k - 1) < a) (ha' : 2 * (m : ℝ) - 1 < a) :
    ∀ᶠ t : ℕ in atTop, c k m t ≤ a ^ t := by
  obtain ⟨hB, hL⟩ := c_bounds k m hk hm1 hm
  apply eventually_le_pow (c_nonneg k m)
  refine eventually_lt_of_limsup_lt (lt_of_le_of_lt hL ?_) hB
  split_ifs <;> assumption

end Puder.Q284T82
end

section
namespace Puder.Q284T82.PartP
open Puder Puder.Q284T82 Filter Topology
/-! q284 T8.2 part P: `nonprim_lower` (non-primitive reduced words of `F_m` have full growth). -/
/-- The abelianization mod 3. -/
noncomputable def Φ (m : ℕ) : FreeGroup (Fin m) →* Multiplicative (Fin m → ZMod 3) :=
  FreeGroup.lift fun j => Multiplicative.ofAdd (Pi.single j 1)

theorem not_prim {m : ℕ} (hm : 1 ≤ m) (w : FreeGroup (Fin m)) (h : Φ m w = 1) :
    ¬ IsPrimitiveIn ⊤ w := by
  classical
  rintro ⟨ι, b, i, hb⟩
  let e : FreeGroup ι ≃* FreeGroup (Fin m) := b.repr.symm.trans Subgroup.topEquiv
  have he : ∀ j, e (FreeGroup.of j) = b j := fun j => rfl
  let eqv : ι ≃ Fin m := Equiv.ofFreeGroupEquiv e
  let _ : Fintype ι := Fintype.ofEquiv (Fin m) eqv.symm
  have hcard : Fintype.card ι = m := by rw [Fintype.card_congr eqv, Fintype.card_fin]
  let ψ : FreeGroup ι →* Multiplicative (Fin m → ZMod 3) := (Φ m).comp e.toMonoidHom
  let f : {j // j ≠ i} → (Fin m → ZMod 3) := fun j => (ψ (FreeGroup.of j.1)).toAdd
  have hmem : ∀ g : FreeGroup ι, (ψ g).toAdd ∈ Submodule.span (ZMod 3) (Set.range f) := by
    intro g
    induction g using FreeGroup.induction_on with
    | C1 => simp
    | of j =>
      by_cases hj : j = i
      · subst hj
        have : ψ (FreeGroup.of j) = 1 := by
          show Φ m (e (FreeGroup.of j)) = 1
          rw [he, hb, h]
        rw [this]; simp
      · exact Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
    | inv_of j hj =>
      rw [map_inv, toAdd_inv]
      exact Submodule.neg_mem _ hj
    | mul x y hx hy =>
      rw [map_mul, toAdd_mul]
      exact Submodule.add_mem _ hx hy
  have htop : Submodule.span (ZMod 3) (Set.range f) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun (ZMod 3) (Fin m)).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have : (ψ (e.symm (FreeGroup.of j))).toAdd = Pi.basisFun (ZMod 3) (Fin m) j := by
      simp [ψ, Φ]
    rw [← this]
    exact hmem _
  have h1 := finrank_range_le_card (R := ZMod 3) f
  rw [Set.finrank, htop, finrank_top, Module.finrank_fin_fun, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq, hcard] at h1
  omega

/-! ## Letter sequences as lists -/
/-- The adjacency relation of reduced letter sequences. -/
def Rl {m : ℕ} (a b : Fin m ⊕ Fin m) : Prop := b ≠ a.swap

theorem NB_iff_chain {m t : ℕ} (i : Fin t → Fin m ⊕ Fin m) :
    NB i ↔ List.IsChain Rl (List.ofFn i) := by
  rw [NB, List.isChain_ofFn]
  constructor
  · intro H j hj
    exact H ⟨j, by omega⟩ hj
  · intro H j hj
    exact H j hj

/-- The weight of a letter in `(ZMod 3)^m`. -/
def wt {m : ℕ} : Fin m ⊕ Fin m → (Fin m → ZMod 3)
  | Sum.inl j => Pi.single j 1
  | Sum.inr j => -Pi.single j 1

/-- The total weight of a list of letters. -/
def σ {m : ℕ} (l : List (Fin m ⊕ Fin m)) : Fin m → ZMod 3 := (l.map wt).sum

theorem σ_append {m : ℕ} (l₁ l₂ : List (Fin m ⊕ Fin m)) : σ (l₁ ++ l₂) = σ l₁ + σ l₂ := by
  simp [σ]

theorem Φ_prod {m : ℕ} (l : List (Fin m ⊕ Fin m)) :
    Φ m (l.map gen).prod = Multiplicative.ofAdd (σ l) := by
  induction l with
  | nil => simp [σ]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, map_mul, ih]
    have : σ (a :: l) = wt a + σ l := by simp [σ]
    rw [this, ofAdd_add]
    congr 1
    rcases a with j | j <;> simp [gen, wt, Φ]

theorem Φ_word {m t : ℕ} (i : Fin t → Fin m ⊕ Fin m) :
    Φ m (word i) = Multiplicative.ofAdd (σ (List.ofFn i)) := by
  rw [word_eq, ← Φ_prod]
  congr 2
  rw [List.map_ofFn]
  rfl

theorem three_nsmul_eq_zero {m : ℕ} (v : Fin m → ZMod 3) (q : ℕ) : (3 * q) • v = 0 := by
  have h3 : ∀ x : ZMod 3, 3 • x = 0 := by decide
  rw [mul_comm, mul_nsmul]
  funext k
  simp only [Pi.smul_apply, Pi.zero_apply]
  exact h3 _

theorem chain_of_isLeft {m : ℕ} (l : List (Fin m ⊕ Fin m)) (h : ∀ a ∈ l, a.isLeft) :
    List.IsChain Rl l := by
  apply List.Pairwise.isChain
  apply List.pairwise_of_forall_mem_list
  intro a ha b hb
  obtain ⟨x, rfl⟩ := Sum.isLeft_iff.1 (h a ha)
  obtain ⟨y, rfl⟩ := Sum.isLeft_iff.1 (h b hb)
  simp [Rl]

theorem σ_replicate {m : ℕ} (n : ℕ) (a : Fin m ⊕ Fin m) :
    σ (List.replicate n a) = n • wt a := by
  simp [σ, List.map_replicate, List.sum_replicate]

theorem σ_flatMap {m : ℕ} {β : Type} (l : List β) (f : β → List (Fin m ⊕ Fin m)) :
    σ (l.flatMap f) = (l.map (fun b => σ (f b))).sum := by
  induction l with
  | nil => simp [σ]
  | cons a l ih => rw [List.flatMap_cons, σ_append, ih, List.map_cons, List.sum_cons]

/-- A zero-weight reduced tail of each length class mod 3. -/
theorem exists_pad {m : ℕ} (hm : 2 ≤ m) (k : ℕ) (hk : k < 3) :
    ∃ P : List (Fin m ⊕ Fin m), P.length % 3 = k ∧ P.length ≤ 5 ∧ List.IsChain Rl P ∧
      (∀ y ∈ P.head?, y.isLeft) ∧ σ P = 0 := by
  interval_cases k
  · exact ⟨[], by simp, by simp, by simp, by simp, by simp [σ]⟩
  · refine ⟨[Sum.inl ⟨0, by omega⟩, Sum.inl ⟨1, by omega⟩, Sum.inr ⟨0, by omega⟩,
      Sum.inr ⟨1, by omega⟩], by simp, by simp, ?_, by simp, ?_⟩
    · simp [Rl, List.isChain_cons_cons]
    · simp [σ, wt]
  · refine ⟨[Sum.inl ⟨0, by omega⟩, Sum.inl ⟨1, by omega⟩, Sum.inl ⟨1, by omega⟩,
      Sum.inl ⟨1, by omega⟩, Sum.inr ⟨0, by omega⟩], by simp, by simp, ?_, by simp, ?_⟩
    · simp [Rl, List.isChain_cons_cons]
    · funext j
      simp only [σ, wt, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        Pi.add_apply, Pi.neg_apply, Pi.zero_apply]
      generalize (Pi.single (⟨0, by omega⟩ : Fin m) (1 : ZMod 3) : Fin m → ZMod 3) j = x
      generalize (Pi.single (⟨1, by omega⟩ : Fin m) (1 : ZMod 3) : Fin m → ZMod 3) j = y
      revert x y; decide

/-- For every weight `c` there is a reduced sequence of length `2m+8` starting with `x_0`. -/
theorem exists_suffix {m : ℕ} (hm : 2 ≤ m) (c : Fin m → ZMod 3) :
    ∃ l : List (Fin m ⊕ Fin m), l.length = 2 * m + 8 ∧ List.IsChain Rl l ∧
      (∀ y ∈ l.head?, y = Sum.inl ⟨0, by omega⟩) ∧ σ l = c := by
  set B : List (Fin m ⊕ Fin m) :=
    (List.finRange m).flatMap fun j => List.replicate (c j).val (Sum.inl j) with hB
  have hBl : B.length ≤ 2 * m := by
    rw [hB, List.length_flatMap]
    have := List.sum_le_card_nsmul ((List.finRange m).map fun j =>
      (List.replicate (c j).val (Sum.inl j : Fin m ⊕ Fin m)).length) 2 (by
        intro x hx
        simp only [List.mem_map, List.length_replicate] at hx
        obtain ⟨j, _, rfl⟩ := hx
        have := ZMod.val_lt (c j)
        omega)
    simpa [Function.comp_def, mul_comm] using this
  have hBσ : σ B = c := by
    rw [hB, σ_flatMap, ← Fin.sum_univ_def]
    conv_rhs => rw [← Finset.univ_sum_single c]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [σ_replicate]
    funext k
    simp [wt, Pi.single_apply]
  have hBl' : ∀ a ∈ B, a.isLeft := by
    intro a ha
    simp only [hB, List.mem_flatMap, List.mem_replicate] at ha
    obtain ⟨j, _, _, rfl⟩ := ha
    rfl
  obtain ⟨P, hP1, hP2, hP3, hP4, hP5⟩ :=
    exists_pad hm ((2 * m + 8 - B.length) % 3) (Nat.mod_lt _ (by norm_num))
  set n0 := 2 * m + 8 - B.length - P.length with hn0
  obtain ⟨q, hq⟩ : ∃ q, n0 = 3 * q := ⟨n0 / 3, by omega⟩
  have hn0pos : 1 ≤ n0 := by omega
  refine ⟨List.replicate n0 (Sum.inl ⟨0, by omega⟩) ++ B ++ P, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_replicate]; omega
  · rw [List.isChain_append]
    refine ⟨chain_of_isLeft _ ?_, hP3, ?_⟩
    · intro a ha
      rcases List.mem_append.1 ha with ha | ha
      · rw [List.eq_of_mem_replicate ha]; rfl
      · exact hBl' a ha
    · intro x hx y hy
      have hx' : x.isLeft := by
        have := List.mem_of_getLast? hx
        rcases List.mem_append.1 this with ha | ha
        · rw [List.eq_of_mem_replicate ha]; rfl
        · exact hBl' x ha
      obtain ⟨a, rfl⟩ := Sum.isLeft_iff.1 hx'
      obtain ⟨b, rfl⟩ := Sum.isLeft_iff.1 (hP4 y hy)
      simp [Rl]
  · intro y hy
    obtain ⟨n1, hn1⟩ : ∃ n1, n0 = n1 + 1 := ⟨n0 - 1, by omega⟩
    rw [hn1, List.replicate_succ] at hy
    simpa using hy.symm
  · rw [σ_append, σ_append, σ_replicate, hq, three_nsmul_eq_zero, hBσ, hP5]
    simp

/-! ## Counting -/
theorem count_A (m r : ℕ) (hm : 2 ≤ m) (y : Fin m ⊕ Fin m) :
    (2 * m - 1 : ℝ) ^ (r + 1) ≤ ((Finset.univ.filter fun u : Fin (r + 2) → Fin m ⊕ Fin m =>
      NB u ∧ u (Fin.last _) ≠ y).card : ℝ) := by
  classical
  refine (pow_le_N m (by omega) (r + 1)).trans ?_
  rw [N_eq_sum, Finset.natCast_card_filter,
    sum_snoc (fun u : Fin (r + 2) → Fin m ⊕ Fin m => if NB u ∧ u (Fin.last _) ≠ y then (1 : ℝ)
      else 0)]
  apply Finset.sum_le_sum
  intro v _
  simp only [NB_snoc_succ, Fin.snoc_last]
  by_cases hv : NB v
  · simp only [hv, true_and, if_true]
    have hpt : ∀ a : Fin m ⊕ Fin m, (1 : ℝ) - (if a = (v (Fin.last r)).swap then 1 else 0) -
        (if a = y then 1 else 0) ≤ if a ≠ (v (Fin.last r)).swap ∧ a ≠ y then 1 else 0 := by
      intro a
      split_ifs <;> simp_all
    refine le_trans ?_ (Finset.sum_le_sum fun a _ => hpt a)
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_sum,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    push_cast
    linarith
  · simp [hv]

/-- A list as a function on `Fin t`. -/
def ofList {α : Type} {t : ℕ} (l : List α) (h : l.length = t) : Fin t → α :=
  fun k => l[k.1]'(by omega)

theorem ofFn_ofList {α : Type} {t : ℕ} (l : List α) (h : l.length = t) :
    List.ofFn (ofList l h) = l := by
  apply List.ext_getElem (by simp [h])
  intro n h1 h2
  simp [ofList]

theorem getLast?_ofFn_succ {α : Type} {n : ℕ} (u : Fin (n + 1) → α) :
    (List.ofFn u).getLast? = some (u (Fin.last n)) := by
  rw [List.ofFn_succ', List.concat_eq_append, List.getLast?_append]
  simp

theorem count_G (m r : ℕ) (hm : 2 ≤ m) :
    (2 * m - 1 : ℝ) ^ (r + 1) ≤
      ((Finset.univ.filter fun i : Fin (r + 2 + (2 * m + 8)) → Fin m ⊕ Fin m =>
        NB i ∧ Φ m (word i) = 1).card : ℝ) := by
  classical
  choose S hSl hSc hSh hSσ using exists_suffix hm
  refine (count_A m r hm (Sum.inr ⟨0, by omega⟩)).trans ?_
  have hlen : ∀ u : Fin (r + 2) → Fin m ⊕ Fin m,
      (List.ofFn u ++ S (-σ (List.ofFn u))).length = r + 2 + (2 * m + 8) := by
    intro u; simp [hSl]; omega
  let F : (Fin (r + 2) → Fin m ⊕ Fin m) → (Fin (r + 2 + (2 * m + 8)) → Fin m ⊕ Fin m) :=
    fun u => ofList _ (hlen u)
  have hF : ∀ u, List.ofFn (F u) = List.ofFn u ++ S (-σ (List.ofFn u)) :=
    fun u => ofFn_ofList _ _
  exact_mod_cast Finset.card_le_card_of_injOn F (by
    intro u hu
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hu ⊢
    refine ⟨?_, ?_⟩
    · rw [NB_iff_chain, hF, List.isChain_append]
      refine ⟨(NB_iff_chain u).1 hu.1, hSc _, ?_⟩
      intro x hx z hz
      rw [getLast?_ofFn_succ, Option.mem_some_iff] at hx
      rw [hSh _ z hz, ← hx]
      intro h
      apply hu.2
      rw [← Sum.swap_swap (u (Fin.last _)), ← h]
      rfl
    · rw [Φ_word, hF, σ_append, hSσ, add_neg_cancel]
      rfl) (by
    intro u _ u' _ h
    have h2 := congrArg List.ofFn h
    rw [hF, hF] at h2
    exact List.ofFn_injective (List.append_inj h2 (by simp)).1)

open Classical in
theorem N_sub_p (m t : ℕ) : N m t - p m t =
    ((Finset.univ.filter fun i : Fin t → Fin m ⊕ Fin m =>
      NB i ∧ ¬ IsPrimitiveIn ⊤ (word i)).card : ℝ) := by
  classical
  have hp : p m t = (((Finset.univ.filter fun i : Fin t → Fin m ⊕ Fin m => NB i).filter
      fun i => IsPrimitiveIn ⊤ (word i)).card : ℝ) := by
    unfold p
    congr 2
    ext i
    simp [NB_iff_length]
  unfold N
  rw [hp, ← Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun i : Fin t → Fin m ⊕ Fin m => NB i)
    (fun i => IsPrimitiveIn ⊤ (word i))]
  push_cast
  rw [add_sub_cancel_left]
  congr 2
  ext i
  simp

theorem nonprim_lower (m : ℕ) (hm : 2 ≤ m) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ t : ℕ in atTop, δ * (2 * m - 1 : ℝ) ^ t ≤ N m t - p m t := by
  classical
  have hq : (0 : ℝ) < 2 * m - 1 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  refine ⟨((2 * m - 1 : ℝ) ^ (2 * m + 9))⁻¹, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (2 * m + 10)] with t ht
  obtain ⟨r, rfl⟩ : ∃ r, t = r + 2 + (2 * m + 8) := ⟨t - (2 * m + 10), by omega⟩
  have he : ((2 * m - 1 : ℝ) ^ (2 * m + 9))⁻¹ * (2 * m - 1 : ℝ) ^ (r + 2 + (2 * m + 8)) =
      (2 * m - 1 : ℝ) ^ (r + 1) := by
    have hX : (2 * m - 1 : ℝ) ^ (2 * m + 9) ≠ 0 := by positivity
    rw [show r + 2 + (2 * m + 8) = (r + 1) + (2 * m + 9) by ring, pow_add _ (r + 1) (2 * m + 9),
      mul_comm ((2 * m - 1 : ℝ) ^ (r + 1)), ← mul_assoc, inv_mul_cancel₀ hX, one_mul]
  rw [he, N_sub_p]
  refine (count_G m r hm).trans ?_
  exact_mod_cast Finset.card_le_card (fun i hi => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact ⟨hi.1, not_prim (by omega) _ hi.2⟩)

end Puder.Q284T82.PartP
end

section
open Filter Topology
namespace Puder.Q284T82
alias nonprim_lower := Puder.Q284T82.PartP.nonprim_lower

/-! ## Lower bound -/
theorem c_lower (k m : ℕ) (hk : 2 ≤ k) (hm2 : 2 ≤ m) (hm : m ≤ k) (a : ℝ)
    (ha : Real.sqrt (2 * k - 1) < a) (ha' : 2 * (m : ℝ) - 2 < a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ t : ℕ in atTop, δ * (2 * m - 1 : ℝ) ^ t - m * a ^ t ≤ c k m t := by
  obtain ⟨δ, hδ, hp⟩ := nonprim_lower m hm2
  refine ⟨δ, hδ, ?_⟩
  have hc : ∀ᶠ t : ℕ in atTop, ∀ m' ∈ Finset.Icc 1 (m - 1), c k m' t ≤ a ^ t := by
    rw [Filter.eventually_all_finset]
    intro m' hm'
    rw [Finset.mem_Icc] at hm'
    apply c_eventually_le k m' hk hm'.1 (by omega) a ha
    have : (m' : ℝ) ≤ m - 1 := by
      have : m' + 1 ≤ m := by omega
      have : ((m' + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast this
      push_cast at this; linarith
    linarith
  filter_upwards [hp, hc, eventually_ge_atTop 1] with t h1 h2 ht
  have hN := N_le k m t hm ht
  have hIcc : Finset.Icc 1 m = insert m (Finset.Icc 1 (m - 1)) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnot : m ∉ Finset.Icc 1 (m - 1) := by simp only [Finset.mem_Icc]; omega
  rw [hIcc, Finset.sum_insert hnot] at hN
  have hs : ∑ m' ∈ Finset.Icc 1 (m - 1), c k m' t ≤ ∑ m' ∈ Finset.Icc 1 (m - 1), a ^ t :=
    Finset.sum_le_sum h2
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at hs
  have ha0 : 0 ≤ a := le_trans (Real.sqrt_nonneg _) ha.le
  have hcard : ((m - 1 + 1 - 1 : ℕ) : ℝ) ≤ m - 1 := by
    have : m - 1 + 1 - 1 + 1 = m := by omega
    have : ((m - 1 + 1 - 1 + 1 : ℕ) : ℝ) = m := by exact_mod_cast this
    push_cast at this ⊢; linarith
  have : ((m - 1 + 1 - 1 : ℕ) : ℝ) * a ^ t ≤ (m - 1) * a ^ t :=
    mul_le_mul_of_nonneg_right hcard (pow_nonneg ha0 t)
  have hat : 0 ≤ a ^ t := pow_nonneg ha0 t
  nlinarith

/-! ## Target -/
theorem _root_.Puder.tendsto_card_reduced_primitivityRank_eq_rpow_of_sqrt_lt_dev (k m : ℕ)
    (hk : 2 ≤ k) (hm : m ≤ k)
    (hlt : Real.sqrt (2 * k - 1) < 2 * m - 1) :
    Tendsto (fun t : ℕ =>
        ((Finset.univ.filter fun i : Fin t → Fin k ⊕ Fin k =>
            (StrongConv.wordFree (List.ofFn fun j => some (i j))).toWord.length = t ∧
              primitivityRank (StrongConv.wordFree (List.ofFn fun j => some (i j))) = m).card : ℝ) ^
          (1 / (t : ℝ))) atTop (𝓝 (2 * m - 1)) := by
  show Tendsto (fun t : ℕ => c k m t ^ (1 / (t : ℝ))) atTop _
  have hk1 : (1 : ℝ) ≤ Real.sqrt (2 * k - 1) := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    rw [Real.le_sqrt' one_pos]; linarith
  have hm2 : 2 ≤ m := by
    by_contra h
    have : (m : ℝ) ≤ 1 := by exact_mod_cast (show m ≤ 1 by omega)
    linarith
  set L : ℝ := 2 * m - 1 with hL
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  rw [tendsto_order]
  constructor
  · intro a ha
    set a' : ℝ := (max (Real.sqrt (2 * k - 1)) (2 * m - 2) + L) / 2 with ha'
    have hmax1 := le_max_left (Real.sqrt (2 * k - 1)) (2 * (m : ℝ) - 2)
    have hmax2 := le_max_right (Real.sqrt (2 * k - 1)) (2 * (m : ℝ) - 2)
    have hmaxL : max (Real.sqrt (2 * k - 1)) (2 * (m : ℝ) - 2) < L :=
      max_lt hlt (by rw [hL]; linarith)
    obtain ⟨δ, hδ, hlow⟩ := c_lower k m hk hm2 hm a' (by rw [ha']; linarith) (by rw [ha']; linarith)
    set b : ℝ := max a (max a' 1) with hb
    have hb1 : 1 ≤ b := le_trans (le_max_right _ _) (le_max_right _ _)
    have hb0 : 0 < b := by linarith
    have hbL : b < L := max_lt ha (max_lt (by rw [ha']; linarith) (by rw [hL]; linarith))
    have hab : a' ≤ b := le_trans (le_max_left _ _) (le_max_right _ _)
    have hgrow : Tendsto (fun t : ℕ => (L / b) ^ t) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by rw [one_lt_div hb0]; exact hbL)
    filter_upwards [hlow, hgrow.eventually_gt_atTop (((m : ℝ) + 1) / δ), eventually_ge_atTop 1]
      with t h1 h2 ht
    have hbt : 0 < b ^ t := pow_pos hb0 t
    have h3 : ((m : ℝ) + 1) * b ^ t < δ * L ^ t := by
      have h2' : ((m : ℝ) + 1) < δ * (L / b) ^ t := by
        rwa [div_lt_iff₀ hδ, mul_comm] at h2
      have := mul_lt_mul_of_pos_right h2' hbt
      rwa [mul_assoc, div_pow, div_mul_cancel₀ _ hbt.ne'] at this
    have h4 : a' ^ t ≤ b ^ t := pow_le_pow_left₀ (by rw [ha']; linarith) hab t
    have h5 : b ^ t < c k m t := by
      have : (m : ℝ) * a' ^ t ≤ m * b ^ t := mul_le_mul_of_nonneg_left h4 (by positivity)
      nlinarith
    calc a ≤ b := le_max_left _ _
      _ = (b ^ t) ^ (1 / (t : ℝ)) := by
        rw [one_div, Real.pow_rpow_inv_natCast hb0.le (by omega)]
      _ < c k m t ^ (1 / (t : ℝ)) :=
        Real.rpow_lt_rpow hbt.le h5 (by
          have : (1 : ℝ) ≤ t := by exact_mod_cast ht
          positivity)
  · intro a ha
    obtain ⟨hB, hLs⟩ := c_bounds k m hk (by omega) hm
    rw [if_neg (not_le.2 hlt)] at hLs
    exact eventually_lt_of_limsup_lt (lt_of_le_of_lt hLs ha) hB

end Puder.Q284T82
end

section
open Filter Topology
open Puder
open Puder.Q284T82
theorem solution (k m : ℕ)
    (hk : 2 ≤ k) (hm : m ≤ k)
    (hlt : Real.sqrt (2 * k - 1) < 2 * m - 1) :
    Tendsto (fun t : ℕ =>
        ((Finset.univ.filter fun i : Fin t → Fin k ⊕ Fin k =>
            (StrongConv.wordFree (List.ofFn fun j => some (i j))).toWord.length = t ∧
              primitivityRank (StrongConv.wordFree (List.ofFn fun j => some (i j))) = m).card : ℝ) ^
          (1 / (t : ℝ))) atTop (𝓝 (2 * m - 1)) := by
  exact Puder.tendsto_card_reduced_primitivityRank_eq_rpow_of_sqrt_lt_dev k m hk hm hlt
end
