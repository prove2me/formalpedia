-- Prove2me | solution 1 for QuantileMDP.cvar_value_achieved
-- status  : ACCEPTED   (prove)
-- author  : @shuffle
-- created : 2026-11-14T02:48:34.00253+00:00
-- url     : https://prove2.me/submissions/a798285c-ad13-4f0b-9bf3-f0eedcc55645

import Definitions.Def_QuantileMDP_achievableLaws
import Mathlib.Data.Set.Finite.Lemmas
import Theorems.Thm_QuantileMDP_eq_7
import Definitions.Def_QuantileMDP_upperCVaR
import Definitions.Def_QuantileMDP_Model

namespace QuantileMDP

/-- Combine a fixed first action with separate continuation policies for each successor. -/
noncomputable def splice {S A : Type*} [DecidableEq S]
    (M : Model S A) (t : ℕ) (s : S) (a : A) (ρ : S → Policy S A) : Policy S A
  | 0, h => if h 0 = s then a else (M.adm_nonempty t (h 0)).choose
  | k + 1, h => ρ (h 1) k (Fin.tail h)

theorem splice_admissible {S A : Type*} [DecidableEq S]
    (M : Model S A) (t : ℕ) (s : S) (a : A) (ha : a ∈ M.adm t s)
    (ρ : S → Policy S A) (hρ : ∀ z, (M.shift (t + 1)).Admissible (ρ z)) :
    (M.shift t).Admissible (splice M t s a ρ) := by
  intro k h
  cases k with
  | zero =>
    have hl : Fin.last 0 = 0 := Fin.eq_zero _
    rw [hl]
    by_cases hh : h 0 = s
    · simpa [splice, Model.shift, hh] using ha
    · simpa [splice, Model.shift, hh] using (M.adm_nonempty t (h 0)).choose_spec
  | succ k =>
    simpa [splice, Model.shift, Fin.tail, Nat.add_left_comm, Nat.add_comm] using
      hρ (h 1) k (Fin.tail h)

/-- Reward laws only depend on the policy on histories starting at the given state. -/
theorem rewardLaw_congr_start {S A : Type*} [Fintype S] (M : Model S A)
    (n : ℕ) (π ρ : Policy S A) (s : S)
    (h : ∀ k (g : Fin (k + 1) → S), g 0 = s → π k g = ρ k g) :
    rewardLaw M n π s = rewardLaw M n ρ s := by
  have hp (g : Fin n → S) (i : Fin n) : pathPrefix (Fin.cons s g) i 0 = s := by
    rfl
  unfold rewardLaw
  apply Finset.sum_congr rfl
  intro g _
  have hw : pathWeight M π (Fin.cons s g) = pathWeight M ρ (Fin.cons s g) := by
    unfold pathWeight
    exact Finset.prod_congr rfl fun i _ => by rw [h _ _ (hp g i)]
  have hr : pathReward M π (Fin.cons s g) = pathReward M ρ (Fin.cons s g) := by
    unfold pathReward
    exact Finset.sum_congr rfl fun i _ => by rw [h _ _ (hp g i)]
  rw [hw, hr]

theorem splice_rewardLaw {S A : Type*} [Fintype S] [DecidableEq S]
    (M : Model S A) (t n : ℕ) (s aState : S) (a : A) (ρ : S → Policy S A) :
    rewardLaw (M.shift (t + 1)) n ((splice M t s a ρ).tail s) aState =
      rewardLaw (M.shift (t + 1)) n (ρ aState) aState := by
  apply rewardLaw_congr_start
  intro k g hg
  simpa [Policy.tail, splice, Fin.tail_cons, Fin.cons_succ] using
    congrArg (fun z => ρ z k g) hg

end QuantileMDP

open MeasureTheory

namespace QuantileMDP

/-- The recursion generates exactly the laws of admissible deterministic
history-dependent policies. -/
theorem mem_achievableLaws_iff {S A : Type*} [Fintype S] [Fintype A]
    (M : Model S A) (n t : ℕ) (s : S) (μ : Measure ℝ) :
    μ ∈ achievableLaws M n t s ↔
      ∃ π : Policy S A, (M.shift t).Admissible π ∧ μ = rewardLaw (M.shift t) n π s := by
  classical
  induction n generalizing t s μ with
  | zero =>
    have hzero (π : Policy S A) : rewardLaw (M.shift t) 0 π s = Measure.dirac 0 := by
      simp [rewardLaw, pathWeight, pathReward]
    simp only [achievableLaws, Set.mem_singleton_iff, hzero]
    constructor
    · intro h
      exact ⟨fun k g => ((M.shift t).adm_nonempty k (g (Fin.last k))).choose,
        fun k g => ((M.shift t).adm_nonempty k (g (Fin.last k))).choose_spec, h⟩
    · exact fun ⟨_, _, h⟩ => h
  | succ n ih =>
    have hlen : t + (n + 1) - t = n + 1 := by omega
    have htail : t + (n + 1) - (t + 1) = n := by omega
    have ht : t < t + (n + 1) := by omega
    have hl (π : Policy S A) (a : A) (hπ : (M.shift t).Admissible π)
        (ha : π 0 (fun _ => s) = a) :
        rewardLaw (M.shift t) (n + 1) π s =
          ∑ i, M.P t s a i • ((rewardLaw (M.shift (t + 1)) n (π.tail s) i).map
            (fun x => x + M.r t s a i)) := by
      simpa only [hlen, htail] using ((eq_7 M (t + (n + 1)) t ht s a).1 π hπ ha)
    change (∃ a ∈ M.adm t s, ∃ ν : S → Measure ℝ,
        (∀ i, ν i ∈ achievableLaws M n (t + 1) i) ∧
          μ = ∑ i, M.P t s a i • (ν i).map (fun x => x + M.r t s a i)) ↔ _
    constructor
    · rintro ⟨a, ha, ν, hν, rfl⟩
      have hρ (i) := (ih (t + 1) i (ν i)).mp (hν i)
      choose ρ hρa hρlaw using hρ
      let π := splice M t s a ρ
      have ha' : π 0 (fun _ => s) = a := by simp [π, splice]
      have hπ := splice_admissible M t s a ha ρ hρa
      refine ⟨π, hπ, ?_⟩
      rw [hl π a hπ ha']
      apply Finset.sum_congr rfl
      intro i _
      rw [hρlaw i, splice_rewardLaw]
    · rintro ⟨π, hπ, rfl⟩
      let a := π 0 (fun _ => s)
      have ha : a ∈ M.adm t s := by simpa [a, Model.shift] using hπ 0 (fun _ => s)
      let ν := fun i => rewardLaw (M.shift (t + 1)) n (π.tail s) i
      refine ⟨a, ha, ν, fun i => (ih (t + 1) i (ν i)).mpr ⟨π.tail s, ?_, rfl⟩, hl π a hπ rfl⟩
      intro k g
      simpa [Policy.tail, Model.shift, Fin.succ_last, Nat.add_left_comm, Nat.add_comm] using
        hπ (k + 1) (Fin.cons s g)

/-- Finiteness follows by taking a finite product of the finite continuation
sets for each action, then taking their images under mixture and translation. -/
theorem achievableLaws_finite {S A : Type*} [Fintype S] [Fintype A]
    (M : Model S A) (n t : ℕ) (s : S) :
    (achievableLaws M n t s).Finite := by
  classical
  induction n generalizing t s with
  | zero => exact Set.finite_singleton _
  | succ n ih =>
    let C := Set.pi Set.univ (fun i => achievableLaws M n (t + 1) i)
    have hC : C.Finite := Set.Finite.pi (fun i => ih (t + 1) i)
    let mix (a : A) (ν : S → Measure ℝ) :=
      ∑ i, M.P t s a i • (ν i).map (fun x => x + M.r t s a i)
    have hf : (⋃ a, mix a '' C).Finite := Set.finite_iUnion fun a => hC.image (mix a)
    apply hf.subset
    rintro μ ⟨a, _, ν, hν, rfl⟩
    exact Set.mem_iUnion.mpr ⟨a, ν, (Set.mem_pi.mpr fun i _ => hν i), rfl⟩

/-- Exact finite-horizon upper-tail CVaR value via the attainable-law
recursion, with the scalar risk objective applied to each full return law. -/
theorem cvar_value_achievableLaws {S A : Type*} [Fintype S] [Fintype A]
    (M : Model S A) (n t : ℕ) (s : S) (τ : ℝ) :
    (⨆ μ ∈ achievableLaws M n t s, (upperCVaR μ τ : EReal)) =
      ⨆ π : {π : Policy S A // (M.shift t).Admissible π},
        (upperCVaR (rewardLaw (M.shift t) n π.val s) τ : EReal) := by
  apply le_antisymm
  · refine iSup_le fun μ => iSup_le fun h => ?_
    obtain ⟨π, hπ, rfl⟩ := (mem_achievableLaws_iff M n t s μ).mp h
    exact le_iSup_of_le ⟨π, hπ⟩ le_rfl
  · refine iSup_le fun π => le_iSup_of_le _ (le_iSup_of_le ?_ le_rfl)
    exact (mem_achievableLaws_iff M n t s _).mpr ⟨π.val, π.property, rfl⟩

/-- The exact finite-horizon CVaR value is attained by a policy. -/
theorem verified_cvar_value_achieved {S A : Type*} [Fintype S] [Fintype A]
    (M : Model S A) (n t : ℕ) (s : S) (τ : ℝ) :
    ∃ π : {π : Policy S A // (M.shift t).Admissible π},
      IsGreatest ((fun μ => upperCVaR μ τ) '' achievableLaws M n t s)
        (upperCVaR (rewardLaw (M.shift t) n π.val s) τ) := by
  let η : Policy S A := fun k h => ((M.shift t).adm_nonempty k (h (Fin.last k))).choose
  have hη : (M.shift t).Admissible η := fun k h =>
    ((M.shift t).adm_nonempty k (h (Fin.last k))).choose_spec
  have hn : (achievableLaws M n t s).Nonempty :=
    ⟨_, (mem_achievableLaws_iff M n t s _).mpr ⟨η, hη, rfl⟩⟩
  obtain ⟨μ, hμ, hmax⟩ := Set.exists_max_image (achievableLaws M n t s)
    (fun μ => upperCVaR μ τ) (achievableLaws_finite M n t s) hn
  obtain ⟨π, hπ, rfl⟩ := (mem_achievableLaws_iff M n t s μ).mp hμ
  refine ⟨⟨π, hπ⟩, ⟨_, hμ, rfl⟩, ?_⟩
  rintro _ ⟨ν, hν, rfl⟩
  exact hmax ν hν

end QuantileMDP

open QuantileMDP

theorem solution {S A : Type*} [Fintype S] [Fintype A]
    (M : Model S A) (n t : ℕ) (s : S) (τ : ℝ) :
    ∃ π : {π : Policy S A // (M.shift t).Admissible π},
      IsGreatest ((fun μ => upperCVaR μ τ) '' achievableLaws M n t s)
        (upperCVaR (rewardLaw (M.shift t) n π.val s) τ) := verified_cvar_value_achieved M n t s τ
