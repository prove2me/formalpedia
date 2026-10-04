-- Prove2me | solution 1 for StochFictPlay.Supermodular.prop53_linear_conjugacy
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T01:30:50.741014+00:00
-- url     : https://prove2.me/submissions/7efc8f96-69ff-4f1d-9736-0001bd8e1af1

import Mathlib
import Definitions.Def_StochFictPlay_Supermodular_ChoiceModel
import Definitions.Def_StochFictPlay_Supermodular_Game
import Definitions.Def_StochFictPlay_Supermodular_StochOrder
import Definitions.Def_StochFictPlay_Supermodular_Dynamics

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory

namespace StochFictPlay.Supermodular.P2MAux8ECB

open StochFictPlay.Supermodular

theorem tie_null {n : ℕ} (j k : Fin n) (hjk : k ≠ j) (c : ℝ) :
    (volume : Measure (Fin n → ℝ)) {e | e k - e j = c} = 0 := by
  let L : (Fin n → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) k -
    LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j
  have hL : ∀ e, L e = e k - e j := fun e => rfl
  have hne : LinearMap.ker L ≠ ⊤ := by
    intro h
    have hmem : (Pi.single k (1:ℝ) : Fin n → ℝ) ∈ LinearMap.ker L := h ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, hL] at hmem
    simp [Ne.symm hjk] at hmem
  have h0 := Measure.addHaar_submodule (volume : Measure (Fin n → ℝ)) _ hne
  have hset : {e : Fin n → ℝ | e k - e j = c} =
      (fun e => e + (-(c • Pi.single k (1:ℝ)))) ⁻¹' (LinearMap.ker L : Set (Fin n → ℝ)) := by
    ext e
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, SetLike.mem_coe, LinearMap.mem_ker, hL]
    simp [Ne.symm hjk]
    constructor <;> intro h <;> linarith
  rw [hset, measure_preimage_add_right]
  exact h0

theorem sum_choiceProb {n : ℕ} (f : (Fin n → ℝ) → ℝ≥0∞) (hf : IsRegularDensity f)
    (π : Fin n → ℝ) (i0 : Fin n) : ∑ j, choiceProb f π j = 1 := by
  set μ : Measure (Fin n → ℝ) := (volume : Measure (Fin n → ℝ)).withDensity f with hμ
  have huniv : μ Set.univ = 1 := by
    rw [hμ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hf.2.2.2.1
  have hac : μ ≪ volume := withDensity_absolutelyContinuous _ _
  let A : Fin n → Set (Fin n → ℝ) := fun i => {e | ∀ j, j ≠ i → π j + e j < π i + e i}
  have hAm : ∀ i, MeasurableSet (A i) := by
    intro i
    have hAi : A i = ⋂ j, ⋂ (_ : j ≠ i), {e : Fin n → ℝ | π j + e j < π i + e i} := by
      ext e; simp [A]
    rw [hAi]
    refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => ?_
    exact measurableSet_lt (by fun_prop) (by fun_prop)
  have hdisj : Pairwise (Function.onFun Disjoint A) := by
    intro a b hab
    rw [Function.onFun, Set.disjoint_left]
    intro e ha hb
    have h1 := ha b (Ne.symm hab)
    have h2 := hb a hab
    linarith
  have hcompl : μ (⋃ i, A i)ᶜ = 0 := by
    apply hac
    apply measure_mono_null
      (t := ⋃ j, ⋃ k, {e : Fin n → ℝ | k ≠ j ∧ e k - e j = π j - π k})
    · intro e he
      simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists] at he
      obtain ⟨j, -, hj⟩ :=
        Finset.exists_max_image Finset.univ (fun m => π m + e m) ⟨i0, Finset.mem_univ _⟩
      have hej := he j
      simp only [A, Set.mem_ofPred_eq, not_forall, not_lt] at hej
      obtain ⟨k, hkj, hk⟩ := hej
      have hk2 := hj k (Finset.mem_univ _)
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
      exact ⟨j, k, hkj, by linarith⟩
    · refine measure_iUnion_null fun j => measure_iUnion_null fun k => ?_
      by_cases hkj : k = j
      · simp [hkj]
      · exact measure_mono_null (fun e he => he.2) (tie_null j k hkj _)
  have hU : μ (⋃ i, A i) = 1 := by
    have := measure_add_measure_compl (μ := μ) (MeasurableSet.iUnion hAm)
    rw [hcompl, add_zero, huniv] at this
    exact this
  have hsum : ∑ j, μ (A j) = 1 := by
    have := measure_iUnion (μ := μ) hdisj hAm
    rw [tsum_fintype] at this
    rw [← this, hU]
  have hfin : ∀ j ∈ (Finset.univ : Finset (Fin n)), μ (A j) ≠ ⊤ := by
    intro j _
    refine ne_top_of_le_ne_top ?_ (measure_mono (Set.subset_univ (A j)))
    rw [huniv]; exact ENNReal.one_ne_top
  show ∑ j, (μ (A j)).toReal = 1
  rw [← ENNReal.toReal_sum hfin, hsum, ENNReal.toReal_one]

theorem simplex_sum {m : ℕ} {y : Fin m → ℝ} (h : y ∈ stdSimplex ℝ (Fin m)) :
    ∑ l, y l = 1 := h.2

theorem simplex_nonneg {m : ℕ} {y : Fin m → ℝ} (h : y ∈ stdSimplex ℝ (Fin m)) :
    ∀ l, 0 ≤ y l := h.1

theorem Tco_sub {m : ℕ} (a b : Fin m → ℝ) : Tco a - Tco b = Tco (a - b) := by
  funext i
  simp only [Tco, Pi.sub_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem tail_pos {m : ℕ} (z : Fin m → ℝ) (k : ℕ) (hk : k ≠ 0) :
    tailMass (Tco z) k = ∑ l : Fin m, if k ≤ l.val then z l else 0 := by
  unfold tailMass
  rw [if_neg hk]
  split_ifs with h
  · show (∑ j : Fin m, if k - 1 < j.val then z j else 0) = _
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : k ≤ l.val
    · rw [if_pos (by omega), if_pos hl]
    · rw [if_neg (by omega), if_neg hl]
  · symm
    refine Finset.sum_eq_zero fun l _ => ?_
    have hl := l.isLt
    have : ¬ k ≤ l.val := by omega
    rw [if_neg this]

theorem tail_simplex {m : ℕ} (x : Fin m → ℝ) (hx : ∑ l, x l = 1) (k : ℕ) :
    tailMass (Tco x) k = ∑ l : Fin m, if k ≤ l.val then x l else 0 := by
  by_cases hk : k = 0
  · subst hk
    simp [tailMass, hx]
  · exact tail_pos x k hk

theorem tail_zero_sum {m : ℕ} (z : Fin m → ℝ) (hz : ∑ l, z l = 0) (k : ℕ) :
    tailMass (Tco z) k - tailMass (m := m) 0 k = ∑ l : Fin m, if k ≤ l.val then z l else 0 := by
  by_cases hk : k = 0
  · subst hk
    simp [tailMass, hz]
  · rw [tail_pos z k hk]
    simp [tailMass, hk]

theorem diff_tail {m : ℕ} (z : Fin m → ℝ) (j : Fin m) :
    (∑ l : Fin m, if j.val ≤ l.val then z l else 0) -
      (∑ l : Fin m, if j.val + 1 ≤ l.val then z l else 0) = z j := by
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    have : b.val ≠ j.val := fun h => hb (Fin.ext h)
    by_cases h1 : j.val ≤ b.val
    · rw [if_pos h1, if_pos (by omega)]; ring
    · rw [if_neg h1, if_neg (by omega)]; ring
  · simp

theorem Tinv_Tco {m : ℕ} (x : Fin m → ℝ) (hx : ∑ l, x l = 1) : Tinv (Tco x) = x := by
  funext j
  show tailMass (Tco x) j.val - tailMass (Tco x) (j.val + 1) = x j
  rw [tail_simplex x hx, tail_simplex x hx]
  exact diff_tail x j

theorem TinvMap_Tmap {p : ℕ} {n : Fin p → ℕ} (x : Mixed n) (hx : x ∈ mixedProfiles n) :
    TinvMap (Tmap x) = x := by
  have hx' : ∀ α, x α ∈ stdSimplex ℝ (Fin (n α)) := hx
  funext α
  exact Tinv_Tco (x α) (simplex_sum (hx' α))

theorem Tmap_mem {p : ℕ} {n : Fin p → ℕ} (x : Mixed n) (hx : x ∈ mixedProfiles n) :
    Tmap x ∈ TSigma n := by
  have hx' : ∀ α, x α ∈ stdSimplex ℝ (Fin (n α)) := hx
  show ∀ α, (∀ i, Tmap x α i ≤ 1 ∧ 0 ≤ Tmap x α i) ∧ Antitone (Tmap x α)
  intro α
  have h0 := simplex_nonneg (hx' α)
  have h1 := simplex_sum (hx' α)
  refine ⟨fun i => ⟨?_, ?_⟩, ?_⟩
  · show (∑ j, if i.val < j.val then x α j else 0) ≤ 1
    rw [← h1]
    refine Finset.sum_le_sum fun j _ => ?_
    split_ifs
    · exact le_refl _
    · exact h0 j
  · show 0 ≤ ∑ j, if i.val < j.val then x α j else 0
    refine Finset.sum_nonneg fun j _ => ?_
    split_ifs
    · exact h0 j
    · exact le_refl _
  · intro i i' hii'
    have hle : i.val ≤ i'.val := hii'
    show (∑ j, if i'.val < j.val then x α j else 0) ≤ ∑ j, if i.val < j.val then x α j else 0
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases ha : i'.val < j.val
    · rw [if_pos ha, if_pos (by omega)]
    · rw [if_neg ha]
      split_ifs
      · exact h0 j
      · exact le_refl _

theorem hasDeriv_Tmap {p : ℕ} {n : Fin p → ℕ} {γ : ℝ → Mixed n} {γ' : Mixed n} {s : Set ℝ}
    {t : ℝ} (h : HasDerivWithinAt γ γ' s t) :
    HasDerivWithinAt (fun r => Tmap (γ r)) (Tmap γ') s t := by
  rw [hasDerivWithinAt_pi]
  intro α
  rw [hasDerivWithinAt_pi]
  intro i
  have hα := hasDerivWithinAt_pi.1 h α
  show HasDerivWithinAt (fun r => ∑ j, if i.val < j.val then γ r α j else 0)
    (∑ j, if i.val < j.val then γ' α j else 0) s t
  apply HasDerivWithinAt.fun_sum
  intro j _
  by_cases hc : i.val < j.val
  · simp only [hc, if_true]
    exact hasDerivWithinAt_pi.1 hα j
  · simp only [hc, if_false]
    exact hasDerivWithinAt_const _ _ _

theorem hasDeriv_tailMass {m : ℕ} {v : ℝ → Fin (m - 1) → ℝ} {v' : Fin (m - 1) → ℝ}
    {s : Set ℝ} {t : ℝ} (h : HasDerivWithinAt v v' s t) (k : ℕ) :
    HasDerivWithinAt (fun r => tailMass (v r) k) (tailMass v' k - tailMass (m := m) 0 k) s t := by
  by_cases hk : k = 0
  · subst hk
    simp only [tailMass, if_true, sub_self]
    exact hasDerivWithinAt_const _ _ _
  · by_cases h2 : k - 1 < m - 1
    · simp only [tailMass, hk, if_false, dif_pos h2, Pi.zero_apply, sub_zero]
      exact hasDerivWithinAt_pi.1 h _
    · simp only [tailMass, hk, if_false, dif_neg h2, sub_self]
      exact hasDerivWithinAt_const _ _ _

theorem hasDeriv_TinvMap {p : ℕ} {n : Fin p → ℕ} {w : ℝ → Coord n} {w' : Coord n}
    {s : Set ℝ} {t : ℝ} (h : HasDerivWithinAt w w' s t) :
    HasDerivWithinAt (fun r => TinvMap (w r))
      (fun α j => (tailMass (w' α) j.val - tailMass (m := n α) 0 j.val) -
        (tailMass (w' α) (j.val + 1) - tailMass (m := n α) 0 (j.val + 1))) s t := by
  rw [hasDerivWithinAt_pi]
  intro α
  rw [hasDerivWithinAt_pi]
  intro j
  have hα := hasDerivWithinAt_pi.1 h α
  exact (hasDeriv_tailMass hα j.val).sub (hasDeriv_tailMass hα (j.val + 1))

end StochFictPlay.Supermodular.P2MAux8ECB

open scoped ENNReal in open StochFictPlay.Supermodular in
theorem solution {p : ℕ} (n : Fin p → ℕ) (hn : ∀ α, 1 ≤ n α)
    (u : (α : Fin p) → Profile n → ℝ)
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞) (hf : ∀ α, IsRegularDensity (f α))
    (γ : ℝ → Mixed n) (hγ : ∀ t : ℝ, 0 ≤ t → γ t ∈ mixedProfiles n) :
    IsSolution (pField f u) (mixedProfiles n) γ ↔
      IsSolution (gField f u) (TSigma n) (fun t => Tmap (γ t)) := by
  constructor
  · rintro ⟨-, hd⟩
    refine ⟨fun t ht => P2MAux8ECB.Tmap_mem _ (hγ t ht), fun t ht => ?_⟩
    have key : gField f u (Tmap (γ t)) = Tmap (pField f u (γ t)) := by
      funext α
      show Tco (pbr f u (TinvMap (Tmap (γ t))) α) - Tco (γ t α) =
        Tco (pbr f u (γ t) α - γ t α)
      rw [P2MAux8ECB.TinvMap_Tmap _ (hγ t ht), P2MAux8ECB.Tco_sub]
    rw [key]
    exact P2MAux8ECB.hasDeriv_Tmap (hd t ht)
  · rintro ⟨-, hd⟩
    refine ⟨hγ, fun t ht => ?_⟩
    have h1 := P2MAux8ECB.hasDeriv_TinvMap (hd t ht)
    have h2 := h1.congr (f₁ := γ)
      (fun r hr => (P2MAux8ECB.TinvMap_Tmap _ (hγ r (le_trans ht hr))).symm)
      (P2MAux8ECB.TinvMap_Tmap _ (hγ t ht)).symm
    convert h2 using 1
    funext α j
    have hγt : ∀ β, γ t β ∈ stdSimplex ℝ (Fin (n β)) := hγ t ht
    have hg : gField f u (Tmap (γ t)) α = Tco (pbr f u (γ t) α - γ t α) := by
      show Tco (pbr f u (TinvMap (Tmap (γ t))) α) - Tco (γ t α) = _
      rw [P2MAux8ECB.TinvMap_Tmap _ (hγ t ht), P2MAux8ECB.Tco_sub]
    have hsum : ∑ l, (pbr f u (γ t) α - γ t α) l = 0 := by
      simp only [Pi.sub_apply, Finset.sum_sub_distrib]
      rw [show ∑ l, pbr f u (γ t) α l = 1 from
        P2MAux8ECB.sum_choiceProb (f α) (hf α) _ ⟨0, hn α⟩, P2MAux8ECB.simplex_sum (hγt α), sub_self]
    show pField f u (γ t) α j =
      (tailMass (gField f u (Tmap (γ t)) α) j.val - tailMass (m := n α) 0 j.val) -
        (tailMass (gField f u (Tmap (γ t)) α) (j.val + 1) - tailMass (m := n α) 0 (j.val + 1))
    rw [hg, P2MAux8ECB.tail_zero_sum _ hsum, P2MAux8ECB.tail_zero_sum _ hsum, P2MAux8ECB.diff_tail]
    rfl
