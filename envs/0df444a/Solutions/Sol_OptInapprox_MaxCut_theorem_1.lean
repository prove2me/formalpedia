-- Prove2me | solution 1 for OptInapprox.MaxCut.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T14:41:09.881929+00:00
-- url     : https://prove2.me/submissions/007cd0fd-d12b-4aea-a543-5142ce46fec1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_ReductionGraph
import Definitions.Def_OptInapprox_MaxCut_MIS
import Definitions.Def_OptInapprox_MaxCut_UGC
import Theorems.Thm_OptInapprox_MaxCut_completeness_8_2
import Theorems.Thm_OptInapprox_MaxCut_soundness_8_3
import Theorems.Thm_SetCoverThreshold_SetCover_gapNPHard_of_reduction
import Theorems.Thm_OptInapprox_MaxCut_reductionGraph_polyTime

namespace OptInapprox.MaxCut.MCX

open Finset

noncomputable section

/-- counting the residue class -/
theorem card_mod_eq (d m i : ℕ) (hi : i < d) :
    ((Finset.range (d * m)).filter (fun j => j % d = i)).card = m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, Finset.range_add, Finset.filter_union, Finset.card_union_of_disjoint, ih]
    · congr 1
      rw [Finset.card_eq_one]
      refine ⟨d * m + i, ?_⟩
      ext j
      simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_range, Finset.mem_singleton,
        addLeftEmbedding_apply]
      constructor
      · rintro ⟨⟨k, hk, rfl⟩, h2⟩
        have : (d * m + k) % d = k := by
          rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hk
        rw [this] at h2; rw [h2]
      · rintro rfl
        refine ⟨⟨i, hi, rfl⟩, ?_⟩
        rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hi
    · apply Finset.disjoint_filter_filter
      rw [Finset.disjoint_left]
      intro j h1 h2
      simp only [Finset.mem_range, Finset.mem_map, addLeftEmbedding_apply] at h1 h2
      obtain ⟨k, _, rfl⟩ := h2
      omega

theorem card_fin_mod_eq (d D i : ℕ) (hi : i < d) (hdD : d ∣ D) :
    (Finset.univ.filter (fun j : Fin D => j.val % d = i)).card = D / d := by
  obtain ⟨m, rfl⟩ := hdD
  have hd : 0 < d := by omega
  rw [Nat.mul_div_cancel_left _ hd]
  have h := card_mod_eq d m i hi
  rw [← Finset.card_map ⟨Fin.val, Fin.val_injective⟩]
  convert h using 2
  ext j
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk, Finset.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩; exact ⟨k.2, hk⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨j, h1⟩, h2, rfl⟩

variable (L : ULC)

/-- degree -/
def deg (v : Fin L.nV) : ℕ := (L.nbrs v).card

theorem deg_le (v : Fin L.nV) : deg L v ≤ L.nW := by
  unfold deg; exact (Finset.card_le_univ _).trans (by simp)

theorem mem_nbrs {v : Fin L.nV} {w : Fin L.nW} : w ∈ L.nbrs v ↔ (v, w) ∈ L.E := by
  simp [ULC.nbrs]

/-- the common multiple of degrees -/
def DD : ℕ := L.nW.factorial

theorem DD_pos : 0 < DD L := Nat.factorial_pos _

theorem deg_dvd (v : Fin L.nV) (h : 0 < deg L v) : deg L v ∣ DD L :=
  Nat.dvd_factorial h (deg_le L v)

/-- copies of left vertices -/
abbrev Cop (K : ℕ) : Type := Σ v : Fin L.nV, Fin (deg L v) × Fin (rgWeight L K v * deg L v)

-- fintype inferred
-- deceq inferred

def eV (K : ℕ) : Fin (Fintype.card (Cop L K)) ≃ Cop L K := (Fintype.equivFin _).symm

def eW (R : ℕ) : Fin (L.nW * R * DD L) ≃ Fin L.nW × Fin R × Fin (DD L) :=
  finProdFinEquiv.symm.trans
    ((Equiv.prodCongr finProdFinEquiv.symm (Equiv.refl _)).trans (Equiv.prodAssoc _ _ _))

/-- the edge predicate of the regularized instance -/
def EP (R K : ℕ) (a : Fin (Fintype.card (Cop L K))) (b : Fin (L.nW * R * DD L)) : Prop :=
  ((eV L K a).1, (eW L R b).1) ∈ L.E ∧ ((eW L R b).2.2 : ℕ) % deg L (eV L K a).1 = (eV L K a).2.1

instance (R K : ℕ) (a) (b) : Decidable (EP L R K a b) := by unfold EP; infer_instance

/-- The regularized Unique Label Cover instance (an analysis device only). -/
@[reducible] def Lpp (R K : ℕ) : ULC where
  nV := Fintype.card (Cop L K)
  nW := L.nW * R * DD L
  M := L.M
  E := Finset.univ.filter fun e => EP L R K e.1 e.2
  σ := fun a b => L.σ (eV L K a).1 (eW L R b).1

variable {L}

theorem Lpp_nbrs (R K : ℕ) (a : Fin (Fintype.card (Cop L K))) :
    (Lpp L R K).nbrs a = Finset.univ.filter (fun b : Fin (L.nW * R * DD L) => EP L R K a b) := by
  ext b; simp [ULC.nbrs, Lpp]

/-- core fiber lemma -/
theorem sum_nbrs_Lpp (R K : ℕ) (a : Fin (Fintype.card (Cop L K))) (g : Fin L.nW → Fin R → ℝ) :
    ∑ b ∈ (Lpp L R K).nbrs a, g (eW L R b).1 (eW L R b).2.1 =
      ((DD L / deg L (eV L K a).1 : ℕ) : ℝ) *
        ∑ w ∈ L.nbrs (eV L K a).1, ∑ r, g w r := by
  rw [Lpp_nbrs, Finset.sum_filter, ← (eW L R).symm.sum_comp]
  simp only [EP, Equiv.apply_symm_apply]
  generalize eV L K a = c
  rcases c with ⟨v, i, s⟩
  simp only [Fintype.sum_prod_type]
  have hd : 0 < deg L v := Nat.lt_of_le_of_lt (Nat.zero_le _) i.2
  rw [Finset.mul_sum, ULC.nbrs, Finset.sum_filter]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases hw : (v, w) ∈ L.E
  · simp only [hw, true_and, if_true]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
      card_fin_mod_eq _ _ _ i.2 (deg_dvd L v hd)]
  · simp [hw]

theorem card_nbrs_Lpp (R K : ℕ) (a : Fin (Fintype.card (Cop L K))) :
    ((Lpp L R K).nbrs a).card = R * DD L := by
  have h := sum_nbrs_Lpp R K a (fun _ _ => (1 : ℝ))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  have hd : 0 < deg L (eV L K a).1 := Nat.lt_of_le_of_lt (Nat.zero_le _) (eV L K a).2.1.2
  have hdv := deg_dvd L _ hd
  have key : (((Lpp L R K).nbrs a).card : ℝ) = ((R * DD L : ℕ) : ℝ) := by
    rw [h]
    change ((DD L / deg L (eV L K a).1 : ℕ) : ℝ) * ((deg L (eV L K a).1 : ℕ) * (R : ℝ)) = _
    rw [← mul_assoc, ← Nat.cast_mul, Nat.div_mul_cancel hdv]
    push_cast; ring
  exact_mod_cast key

theorem card_Cop_pos (K : ℕ) (hK : 0 < K) (hE : L.E.Nonempty) : 0 < Fintype.card (Cop L K) := by
  obtain ⟨⟨v, w⟩, hvw⟩ := hE
  have hw : w ∈ L.nbrs v := (mem_nbrs L).2 hvw
  have hd : 0 < deg L v := Finset.card_pos.2 ⟨w, hw⟩
  have ht : 0 < rgWeight L K v := by
    unfold rgWeight
    apply Nat.div_pos _ hd
    calc (L.nbrs v).card ≤ L.nW := deg_le L v
      _ ≤ K * L.nW := Nat.le_mul_of_pos_left _ hK
  have : Nonempty (Cop L K) := ⟨⟨v, ⟨0, hd⟩, ⟨0, Nat.mul_pos ht hd⟩⟩⟩
  exact Fintype.card_pos

theorem Lpp_regular (R K : ℕ) (hR : 0 < R) (hK : 0 < K) (hE : L.E.Nonempty) :
    (Lpp L R K).IsVRegular :=
  ⟨card_Cop_pos K hK hE, R * DD L, Nat.mul_pos hR (DD_pos L), fun a => card_nbrs_Lpp R K a⟩

/-- the acceptance test on the `R`-fold Long Code tables -/
def accT {R : ℕ} (F : Fin L.nW → Fin R → (Fin L.M → Bool) → Bool) (ρ : ℝ) (v : Fin L.nV)
    (w w' : Fin L.nW) (r r' : Fin R) : ℝ :=
  (2 ^ L.M : ℝ)⁻¹ * ∑ x, ∑ μ, muWeight ρ μ *
    (if F w r (compose x (L.σ v w)) ≠ F w' r' (coordMul (compose x (L.σ v w')) μ) then 1 else 0)

def Fpp (R K : ℕ) (F : Fin L.nW → Fin R → (Fin L.M → Bool) → Bool) :
    Fin (Lpp L R K).nW → (Fin (Lpp L R K).M → Bool) → Bool :=
  fun b => F (eW L R b).1 (eW L R b).2.1

theorem sum_Cop (K : ℕ) (f : Fin L.nV → ℝ) :
    ∑ a : Fin (Fintype.card (Cop L K)), f (eV L K a).1 =
      ∑ v, ((deg L v * (rgWeight L K v * deg L v) : ℕ) : ℝ) * f v := by
  rw [(eV L K).sum_comp (fun c => f c.1)]
  change ∑ c : (Σ v : Fin L.nV, Fin (deg L v) × Fin (rgWeight L K v * deg L v)), f c.1 = _
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]

theorem accProb_Lpp (R K : ℕ) (hR : 0 < R) (ρ : ℝ)
    (F : Fin L.nW → Fin R → (Fin L.M → Bool) → Bool) :
    accProb (Lpp L R K) ρ (Fpp R K F) = (Fintype.card (Cop L K) : ℝ)⁻¹ *
      ∑ v, (rgWeight L K v : ℝ) * ((R : ℝ)⁻¹ ^ 2 *
        ∑ w ∈ L.nbrs v, ∑ w' ∈ L.nbrs v, ∑ r, ∑ r', accT F ρ v w w' r r') := by
  unfold accProb
  congr 1
  have step : ∀ a : Fin (Fintype.card (Cop L K)),
      (((Lpp L R K).nbrs a).card : ℝ)⁻¹ ^ 2 *
        ∑ b ∈ (Lpp L R K).nbrs a, ∑ b' ∈ (Lpp L R K).nbrs a, (2 ^ (Lpp L R K).M : ℝ)⁻¹ *
          ∑ x, ∑ μ, muWeight ρ μ *
            (if Fpp R K F b (compose x ((Lpp L R K).σ a b)) ≠
                Fpp R K F b' (coordMul (compose x ((Lpp L R K).σ a b')) μ) then 1 else 0) =
      (fun v => if deg L v = 0 then 0 else
        ((deg L v * (rgWeight L K v * deg L v) : ℕ) : ℝ)⁻¹ * ((rgWeight L K v : ℝ) * ((R : ℝ)⁻¹ ^ 2 *
        ∑ w ∈ L.nbrs v, ∑ w' ∈ L.nbrs v, ∑ r, ∑ r', accT F ρ v w w' r r'))) (eV L K a).1 := by
    intro a
    have hd : 0 < deg L (eV L K a).1 := Nat.lt_of_le_of_lt (Nat.zero_le _) (eV L K a).2.1.2
    have hdv := deg_dvd L _ hd
    rw [card_nbrs_Lpp]
    have inner : ∀ b : Fin (L.nW * R * DD L),
        ∑ b' ∈ (Lpp L R K).nbrs a, (2 ^ (Lpp L R K).M : ℝ)⁻¹ *
          ∑ x, ∑ μ, muWeight ρ μ *
            (if Fpp R K F b (compose x ((Lpp L R K).σ a b)) ≠
                Fpp R K F b' (coordMul (compose x ((Lpp L R K).σ a b')) μ) then 1 else 0) =
        ((DD L / deg L (eV L K a).1 : ℕ) : ℝ) * ∑ w' ∈ L.nbrs (eV L K a).1, ∑ r',
          accT F ρ (eV L K a).1 (eW L R b).1 w' (eW L R b).2.1 r' := by
      intro b
      exact sum_nbrs_Lpp R K a (fun w' r' => accT F ρ (eV L K a).1 (eW L R b).1 w' (eW L R b).2.1 r')
    rw [Finset.sum_congr rfl (fun b _ => inner b)]
    rw [← Finset.mul_sum]
    rw [sum_nbrs_Lpp R K a (fun w r => ∑ w' ∈ L.nbrs (eV L K a).1, ∑ r',
          accT F ρ (eV L K a).1 w w' r r')]
    simp only [Nat.pos_iff_ne_zero.1 hd, if_false]
    have ht : 0 < rgWeight L K (eV L K a).1 * deg L (eV L K a).1 :=
      Nat.lt_of_le_of_lt (Nat.zero_le _) (eV L K a).2.2.2
    generalize (eV L K a).1 = v at hd hdv ht ⊢
    have hreorder : ∑ w ∈ L.nbrs v, ∑ r, ∑ w' ∈ L.nbrs v, ∑ r', accT F ρ v w w' r r' =
        ∑ w ∈ L.nbrs v, ∑ w' ∈ L.nbrs v, ∑ r, ∑ r', accT F ρ v w w' r r' := by
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [Finset.sum_comm]
    rw [hreorder]
    generalize (∑ w ∈ L.nbrs v, ∑ w' ∈ L.nbrs v, ∑ r, ∑ r', accT F ρ v w w' r r') = S
    have hD : ((DD L / deg L v : ℕ) : ℝ) * (deg L v : ℝ) = (DD L : ℝ) := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel hdv]
    have hdR : (deg L v : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    have htR : (rgWeight L K v : ℝ) ≠ 0 := by
      have : 0 < rgWeight L K v := Nat.pos_of_mul_pos_right ht
      exact_mod_cast this.ne'
    have hRR : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
    have hDR : (DD L : ℝ) ≠ 0 := by exact_mod_cast (DD_pos L).ne'
    have hq : ((DD L / deg L v : ℕ) : ℝ) = (DD L : ℝ) / deg L v := by
      field_simp; linarith [hD]
    rw [hq]
    push_cast
    field_simp
  rw [Finset.sum_congr rfl (fun a _ => step a)]
  have hC := sum_Cop (L := L) K (fun v => if deg L v = 0 then 0 else
        ((deg L v * (rgWeight L K v * deg L v) : ℕ) : ℝ)⁻¹ * ((rgWeight L K v : ℝ) * ((R : ℝ)⁻¹ ^ 2 *
        ∑ w ∈ L.nbrs v, ∑ w' ∈ L.nbrs v, ∑ r, ∑ r', accT F ρ v w w' r r')))
  refine hC.trans ?_
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases hd : deg L v = 0
  · have : L.nbrs v = ∅ := Finset.card_eq_zero.1 hd
    simp [hd, this]
  · simp only [hd, if_false]
    by_cases ht : rgWeight L K v = 0
    · simp [ht]
    · rw [← mul_assoc, mul_inv_cancel₀ (by
        have : 0 < deg L v * (rgWeight L K v * deg L v) :=
          Nat.mul_pos (Nat.pos_of_ne_zero hd) (Nat.mul_pos (Nat.pos_of_ne_zero ht)
            (Nat.pos_of_ne_zero hd))
        exact_mod_cast this.ne'), one_mul]

theorem card_filter_E (L' : ULC) (Q : Fin L'.nV → Fin L'.nW → Prop)
    [∀ v w, Decidable (Q v w)] :
    ((L'.E.filter fun e => Q e.1 e.2).card : ℝ) =
      ∑ v, ∑ w ∈ L'.nbrs v, if Q v w then (1 : ℝ) else 0 := by
  rw [Finset.card_filter, Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [show (L'.E) = Finset.univ.filter (fun e => e ∈ L'.E) by ext; simp]
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [ULC.nbrs, Finset.sum_filter]

theorem card_E_eq (L' : ULC) : (L'.E.card : ℝ) = ∑ v, ((L'.nbrs v).card : ℝ) := by
  have h := card_filter_E L' (fun _ _ => True)
  simp only [Finset.filter_true_of_mem (fun _ _ => trivial), if_true, Finset.sum_const,
    nsmul_eq_mul, mul_one] at h
  exact h

theorem satFrac_eq (L' : ULC) (lab : (Fin L'.nV → Fin L'.M) × (Fin L'.nW → Fin L'.M)) :
    L'.satFrac lab = (∑ v, ∑ w ∈ L'.nbrs v,
      if L'.σ v w (lab.2 w) = lab.1 v then (1 : ℝ) else 0) / ∑ v, ((L'.nbrs v).card : ℝ) := by
  rw [ULC.satFrac, ← card_E_eq]
  congr 1
  exact card_filter_E L' (fun v w => L'.σ v w (lab.2 w) = lab.1 v)

theorem satFrac_le_OPT (L' : ULC) (lab : (Fin L'.nV → Fin L'.M) × (Fin L'.nW → Fin L'.M)) :
    L'.satFrac lab ≤ L'.OPT :=
  le_ciSup (Set.finite_range _).bddAbove lab

theorem satFrac_nonneg (L' : ULC) (lab : (Fin L'.nV → Fin L'.M) × (Fin L'.nW → Fin L'.M)) :
    0 ≤ L'.satFrac lab := by
  unfold ULC.satFrac; positivity

theorem OPT_nonneg (L' : ULC) : 0 ≤ L'.OPT :=
  Real.iSup_nonneg (satFrac_nonneg L')

theorem weight_le (v : Fin L.nV) : rgWeight L 2 v * deg L v ≤ 2 * L.nW := by
  unfold rgWeight deg; exact Nat.div_mul_le_self _ _

theorem weight_ge (v : Fin L.nV) (hd : 0 < deg L v) : L.nW ≤ rgWeight L 2 v * deg L v := by
  unfold rgWeight
  have h1 := Nat.div_add_mod (2 * L.nW) (deg L v)
  have h2 := Nat.mod_lt (2 * L.nW) hd
  have h3 := deg_le L v
  unfold deg at *
  rw [mul_comm] at h1
  omega

theorem ratio_bound {ι : Type} (S : Finset ι) (a d s : ι → ℝ) (A : ℝ) (hA : 0 < A)
    (ha_le : ∀ v ∈ S, a v ≤ 2 * A) (ha_ge : ∀ v ∈ S, 0 < d v → A ≤ a v)
    (hs0 : ∀ v ∈ S, 0 ≤ s v) (hsd : ∀ v ∈ S, s v ≤ d v) (hE : 0 < ∑ v ∈ S, d v) :
    1 - 2 * (1 - (∑ v ∈ S, s v) / ∑ v ∈ S, d v) ≤
      (∑ v ∈ S, a v * s v) / ∑ v ∈ S, a v * d v := by
  have hX : A * ∑ v ∈ S, d v ≤ ∑ v ∈ S, a v * d v := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun v hv => ?_
    rcases (le_trans (hs0 v hv) (hsd v hv)).lt_or_eq with h | h
    · exact mul_le_mul_of_nonneg_right (ha_ge v hv h) h.le
    · rw [← h]; simp
  have hY : ∑ v ∈ S, a v * d v - ∑ v ∈ S, a v * s v ≤
      2 * A * (∑ v ∈ S, d v - ∑ v ∈ S, s v) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun v hv => ?_
    rw [← mul_sub]
    exact mul_le_mul_of_nonneg_right (ha_le v hv) (by linarith [hsd v hv])
  have hXpos : 0 < ∑ v ∈ S, a v * d v := lt_of_lt_of_le (mul_pos hA hE) hX
  have hSE : ∑ v ∈ S, s v ≤ ∑ v ∈ S, d v := Finset.sum_le_sum hsd
  generalize ∑ v ∈ S, a v * d v = X at *
  generalize ∑ v ∈ S, a v * s v = Y at *
  generalize ∑ v ∈ S, d v = E at *
  generalize ∑ v ∈ S, s v = Sm at *
  rw [le_div_iff₀ hXpos]
  set u := Sm / E with hu_def
  have hu : Sm = u * E := by rw [hu_def]; field_simp
  have h1u : 0 ≤ 1 - u := by
    rw [hu_def, sub_nonneg, div_le_one hE]; exact hSE
  have h2 : A * E * (1 - u) ≤ X * (1 - u) := mul_le_mul_of_nonneg_right hX h1u
  have h3 : X - Y ≤ 2 * (A * E * (1 - u)) := by rw [hu] at hY; nlinarith
  nlinarith

def liftLab (R K : ℕ) (lab : (Fin L.nV → Fin L.M) × (Fin L.nW → Fin L.M)) :
    (Fin (Lpp L R K).nV → Fin (Lpp L R K).M) × (Fin (Lpp L R K).nW → Fin (Lpp L R K).M) :=
  (fun a => lab.1 (eV L K a).1, fun b => lab.2 (eW L R b).1)

/-- number of satisfied edges at `v` -/
def satAt (lab : (Fin L.nV → Fin L.M) × (Fin L.nW → Fin L.M)) (v : Fin L.nV) : ℝ :=
  ∑ w ∈ L.nbrs v, if L.σ v w (lab.2 w) = lab.1 v then (1 : ℝ) else 0

theorem satAt_le (lab : (Fin L.nV → Fin L.M) × (Fin L.nW → Fin L.M)) (v : Fin L.nV) :
    satAt lab v ≤ (deg L v : ℝ) := by
  unfold satAt deg
  calc _ ≤ ∑ w ∈ L.nbrs v, (1 : ℝ) := Finset.sum_le_sum fun w _ => by split_ifs <;> norm_num
    _ = _ := by simp

theorem satAt_nonneg (lab : (Fin L.nV → Fin L.M) × (Fin L.nW → Fin L.M)) (v : Fin L.nV) :
    0 ≤ satAt lab v := by
  unfold satAt; exact Finset.sum_nonneg fun w _ => by split_ifs <;> norm_num

theorem card_Cop_eq (K : ℕ) : (Fintype.card (Cop L K) : ℝ) =
    ∑ v, ((deg L v * (rgWeight L K v * deg L v) : ℕ) : ℝ) := by
  have h := sum_Cop (L := L) K (fun _ => (1 : ℝ))
  simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  exact h

theorem satFrac_Lpp_lift (R K : ℕ) (hR : 0 < R)
    (lab : (Fin L.nV → Fin L.M) × (Fin L.nW → Fin L.M)) :
    (Lpp L R K).satFrac (liftLab R K lab) =
      (∑ v, ((rgWeight L K v * deg L v : ℕ) : ℝ) * satAt lab v) /
        ∑ v, ((rgWeight L K v * deg L v : ℕ) : ℝ) * (deg L v : ℝ) := by
  rw [satFrac_eq]
  have hnum : ∑ a, ∑ b ∈ (Lpp L R K).nbrs a,
      (if (Lpp L R K).σ a b ((liftLab R K lab).2 b) = (liftLab R K lab).1 a then (1 : ℝ) else 0)
      = ∑ a : Fin (Fintype.card (Cop L K)), (fun v => ((DD L / deg L v : ℕ) : ℝ) *
          ∑ w ∈ L.nbrs v, ∑ _r : Fin R, if L.σ v w (lab.2 w) = lab.1 v then (1 : ℝ) else 0)
          (eV L K a).1 :=
    Finset.sum_congr rfl fun a _ =>
      sum_nbrs_Lpp R K a (fun w _ => if L.σ (eV L K a).1 w (lab.2 w) = lab.1 (eV L K a).1
        then (1 : ℝ) else 0)
  have hden : ∑ a : Fin (Lpp L R K).nV, (((Lpp L R K).nbrs a).card : ℝ) =
      ∑ a : Fin (Fintype.card (Cop L K)), (fun _ => ((R * DD L : ℕ) : ℝ)) (eV L K a).1 :=
    Finset.sum_congr rfl fun a _ => by rw [card_nbrs_Lpp]
  rw [hnum, hden]
  rw [sum_Cop K (fun v => ((DD L / deg L v : ℕ) : ℝ) *
          ∑ w ∈ L.nbrs v, ∑ _r : Fin R, if L.σ v w (lab.2 w) = lab.1 v then (1 : ℝ) else 0),
    sum_Cop K (fun _ => ((R * DD L : ℕ) : ℝ))]
  have hRD : (0 : ℝ) < ((R * DD L : ℕ) : ℝ) := by
    have := Nat.mul_pos hR (DD_pos L); exact_mod_cast this
  have e1 : ∀ v, ((deg L v * (rgWeight L K v * deg L v) : ℕ) : ℝ) *
      (((DD L / deg L v : ℕ) : ℝ) * ∑ w ∈ L.nbrs v, ∑ _r : Fin R,
        if L.σ v w (lab.2 w) = lab.1 v then (1 : ℝ) else 0) =
      ((rgWeight L K v * deg L v : ℕ) : ℝ) * satAt lab v * ((R * DD L : ℕ) : ℝ) := by
    intro v
    by_cases hd : deg L v = 0
    · have : L.nbrs v = ∅ := Finset.card_eq_zero.1 hd
      simp [hd, this, satAt]
    · have hdv := deg_dvd L v (Nat.pos_of_ne_zero hd)
      have hD : ((DD L / deg L v : ℕ) : ℝ) * (deg L v : ℝ) = (DD L : ℝ) := by
        rw [← Nat.cast_mul, Nat.div_mul_cancel hdv]
      unfold satAt
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← Finset.mul_sum]
      push_cast
      rw [← hD]; ring
  have e2 : ∀ v, ((deg L v * (rgWeight L K v * deg L v) : ℕ) : ℝ) * ((R * DD L : ℕ) : ℝ) =
      ((rgWeight L K v * deg L v : ℕ) : ℝ) * (deg L v : ℝ) * ((R * DD L : ℕ) : ℝ) := by
    intro v; push_cast; ring
  simp only [e1, e2]
  rw [← Finset.sum_mul, ← Finset.sum_mul, mul_div_mul_right _ _ hRD.ne']

theorem satFrac_lift (R : ℕ) (hR : 0 < R) (hE : L.E.Nonempty)
    (lab : (Fin L.nV → Fin L.M) × (Fin L.nW → Fin L.M)) :
    1 - 2 * (1 - L.satFrac lab) ≤ (Lpp L R 2).satFrac (liftLab R 2 lab) := by
  rw [satFrac_Lpp_lift R 2 hR, satFrac_eq L]
  have hEpos : 0 < ∑ v, ((L.nbrs v).card : ℝ) := by
    rw [← card_E_eq]; exact_mod_cast hE.card_pos
  have hnW : 0 < L.nW := by
    obtain ⟨⟨v, w⟩, _⟩ := hE; exact Nat.lt_of_le_of_lt (Nat.zero_le _) w.2
  exact ratio_bound Finset.univ (fun v => ((rgWeight L 2 v * deg L v : ℕ) : ℝ))
    (fun v => (deg L v : ℝ)) (satAt lab) (L.nW : ℝ) (by exact_mod_cast hnW)
    (fun v _ => by have := weight_le (L := L) v; exact_mod_cast this)
    (fun v _ hd => by
      have := weight_ge (L := L) v (by exact_mod_cast hd); exact_mod_cast this)
    (fun v _ => satAt_nonneg lab v) (fun v _ => satAt_le lab v) hEpos

theorem sum_Cop_mod (K D : ℕ) (j : Fin D) (f : Fin L.nV → ℝ) :
    ∑ a : Fin (Fintype.card (Cop L K)),
      (if (j : ℕ) % deg L (eV L K a).1 = (eV L K a).2.1 then f (eV L K a).1 else 0) =
      ∑ v, ((rgWeight L K v * deg L v : ℕ) : ℝ) * f v := by
  rw [(eV L K).sum_comp (fun c => if (j : ℕ) % deg L c.1 = c.2.1 then f c.1 else 0)]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  by_cases hd : deg L v = 0
  · have : IsEmpty (Fin (deg L v)) := by rw [hd]; infer_instance
    simp [hd]
  · have hlt : (j : ℕ) % deg L v < deg L v := Nat.mod_lt _ (Nat.pos_of_ne_zero hd)
    have : ∀ i : Fin (deg L v), ((j : ℕ) % deg L v = i ↔ i = ⟨_, hlt⟩) := by
      intro i; constructor
      · intro h; ext; exact h.symm
      · intro h; rw [h]
    simp only [this, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ (⟨_, hlt⟩ : Fin (deg L v))]
    simp only [Finset.mem_univ, if_true]

theorem satFrac_Lpp_le (R : ℕ) (hR : 0 < R) (hE : L.E.Nonempty)
    (lab : (Fin (Lpp L R 2).nV → Fin (Lpp L R 2).M) × (Fin (Lpp L R 2).nW → Fin (Lpp L R 2).M)) :
    (Lpp L R 2).satFrac lab ≤ 2 * L.OPT := by
  have hM : 0 < L.M := by
    have := card_Cop_pos (L := L) 2 (by norm_num) hE
    exact Nat.lt_of_le_of_lt (Nat.zero_le _) (lab.1 ⟨0, this⟩).2
  have hnW : 0 < L.nW := by
    obtain ⟨⟨v, w⟩, _⟩ := hE; exact Nat.lt_of_le_of_lt (Nat.zero_le _) w.2
  -- counts and argmax
  let cnt : Fin L.nV → (Fin L.nW → Fin L.M) → Fin L.M → ℝ := fun v W' ℓ =>
    ∑ w ∈ L.nbrs v, if L.σ v w (W' w) = ℓ then (1 : ℝ) else 0
  have hex : ∀ v (W' : Fin L.nW → Fin L.M), ∃ ℓ, ∀ ℓ', cnt v W' ℓ' ≤ cnt v W' ℓ := by
    intro v W'
    obtain ⟨ℓ, _, h⟩ := Finset.exists_max_image Finset.univ (cnt v W')
      ⟨⟨0, hM⟩, Finset.mem_univ _⟩
    exact ⟨ℓ, fun ℓ' => h ℓ' (Finset.mem_univ _)⟩
  choose amax hamax using hex
  let Wl : Fin R → Fin (DD L) → Fin L.nW → Fin L.M := fun r j w => lab.2 ((eW L R).symm (w, r, j))
  -- satisfied count of the decoded labeling
  have hdec : ∀ r j, ∑ v, cnt v (Wl r j) (amax v (Wl r j)) ≤ (L.E.card : ℝ) * L.OPT := by
    intro r j
    have h1 := satFrac_le_OPT L (fun v => amax v (Wl r j), Wl r j)
    rw [satFrac_eq, ← card_E_eq] at h1
    have hEc : (0 : ℝ) < L.E.card := by exact_mod_cast hE.card_pos
    rw [div_le_iff₀ hEc] at h1
    linarith
  rw [satFrac_eq]
  have hden : ∑ a : Fin (Lpp L R 2).nV, (((Lpp L R 2).nbrs a).card : ℝ) =
      ((R * DD L : ℕ) : ℝ) * ∑ v, ((deg L v * (rgWeight L 2 v * deg L v) : ℕ) : ℝ) := by
    rw [Finset.sum_congr rfl (fun a _ => show (((Lpp L R 2).nbrs a).card : ℝ) =
      ((R * DD L : ℕ) : ℝ) by rw [card_nbrs_Lpp])]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      show ((Lpp L R 2).nV : ℝ) = (Fintype.card (Cop L 2) : ℝ) from rfl, card_Cop_eq]
    ring
  rw [hden]
  have hterm : ∀ a : Fin (Fintype.card (Cop L 2)),
      ∑ b ∈ (Lpp L R 2).nbrs a,
        (if (Lpp L R 2).σ a b (lab.2 b) = lab.1 a then (1 : ℝ) else 0) ≤
      ∑ r : Fin R, ∑ j : Fin (DD L), (if (j : ℕ) % deg L (eV L 2 a).1 = (eV L 2 a).2.1 then
        cnt (eV L 2 a).1 (Wl r j) (amax (eV L 2 a).1 (Wl r j)) else 0) := by
    intro a
    rw [Lpp_nbrs, Finset.sum_filter, ← (eW L R).symm.sum_comp]
    simp only [EP, Equiv.apply_symm_apply]
    rw [Fintype.sum_prod_type, Finset.sum_comm, Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun j _ => ?_
    simp only []
    split_ifs with hj
    · refine le_trans (le_of_eq ?_) (hamax (eV L 2 a).1 (Wl r j) (lab.1 a))
      simp only [cnt, ULC.nbrs, Finset.sum_filter, hj, and_true]
      refine Finset.sum_congr rfl fun w _ => ?_
      by_cases hw : ((eV L 2 a).1, w) ∈ L.E
      · simp [hw, Wl]
      · simp [hw]
    · apply le_of_eq
      refine Finset.sum_eq_zero fun w _ => ?_
      simp [hj]
  have hnum : ∑ a : Fin (Lpp L R 2).nV, ∑ b ∈ (Lpp L R 2).nbrs a,
        (if (Lpp L R 2).σ a b (lab.2 b) = lab.1 a then (1 : ℝ) else 0) ≤
      ((R * DD L : ℕ) : ℝ) * (((2 * L.nW : ℕ) : ℝ) * ((L.E.card : ℝ) * L.OPT)) := by
    refine le_trans (Finset.sum_le_sum fun a _ => hterm a) ?_
    rw [Finset.sum_comm]
    have hb : ∀ r : Fin R, ∑ a : Fin (Fintype.card (Cop L 2)), ∑ j : Fin (DD L),
        (if (j : ℕ) % deg L (eV L 2 a).1 = (eV L 2 a).2.1 then
          cnt (eV L 2 a).1 (Wl r j) (amax (eV L 2 a).1 (Wl r j)) else 0) ≤
        ∑ _j : Fin (DD L), ((2 * L.nW : ℕ) : ℝ) * ((L.E.card : ℝ) * L.OPT) := by
      intro r
      rw [Finset.sum_comm]
      refine Finset.sum_le_sum fun j _ => ?_
      rw [sum_Cop_mod (L := L) 2 (DD L) j (fun v => cnt v (Wl r j) (amax v (Wl r j)))]
      calc ∑ v, ((rgWeight L 2 v * deg L v : ℕ) : ℝ) * cnt v (Wl r j) (amax v (Wl r j))
          ≤ ∑ v, ((2 * L.nW : ℕ) : ℝ) * cnt v (Wl r j) (amax v (Wl r j)) := by
            refine Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_right ?_ ?_
            · exact_mod_cast weight_le (L := L) v
            · exact Finset.sum_nonneg fun w _ => by split_ifs <;> norm_num
        _ = ((2 * L.nW : ℕ) : ℝ) * ∑ v, cnt v (Wl r j) (amax v (Wl r j)) := by
            rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left (hdec r j) (by positivity)
    refine le_trans (Finset.sum_le_sum fun r _ => hb r) ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring_nf; exact le_refl _
  have hden2 : ((R * DD L : ℕ) : ℝ) * ((L.nW : ℝ) * (L.E.card : ℝ)) ≤
      ((R * DD L : ℕ) : ℝ) * ∑ v, ((deg L v * (rgWeight L 2 v * deg L v) : ℕ) : ℝ) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [card_E_eq, Finset.mul_sum]
    refine Finset.sum_le_sum fun v _ => ?_
    by_cases hd : deg L v = 0
    · simp [show (L.nbrs v).card = 0 from hd, hd]
    · have := weight_ge (L := L) v (Nat.pos_of_ne_zero hd)
      have h2 : deg L v * L.nW ≤ deg L v * (rgWeight L 2 v * deg L v) :=
        Nat.mul_le_mul_left _ this
      have h3 : ((deg L v * L.nW : ℕ) : ℝ) ≤ ((deg L v * (rgWeight L 2 v * deg L v) : ℕ) : ℝ) := by
        exact_mod_cast h2
      unfold deg at h3 ⊢
      push_cast at h3 ⊢
      linarith
  have hpos : (0 : ℝ) < ((R * DD L : ℕ) : ℝ) * ((L.nW : ℝ) * (L.E.card : ℝ)) := by
    have : 0 < R * DD L := Nat.mul_pos hR (DD_pos L)
    have hEc : (0 : ℝ) < L.E.card := by exact_mod_cast hE.card_pos
    have : (0 : ℝ) < L.nW := by exact_mod_cast hnW
    positivity
  rw [div_le_iff₀ (lt_of_lt_of_le hpos hden2)]
  have hOPT := OPT_nonneg L
  calc _ ≤ ((R * DD L : ℕ) : ℝ) * (((2 * L.nW : ℕ) : ℝ) * ((L.E.card : ℝ) * L.OPT)) := hnum
    _ = 2 * L.OPT * (((R * DD L : ℕ) : ℝ) * ((L.nW : ℝ) * (L.E.card : ℝ))) := by push_cast; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hden2 (by positivity)

end

end OptInapprox.MaxCut.MCX


namespace OptInapprox.MaxCut.MCX

open Finset

noncomputable section

variable {L : ULC}

theorem sum_muNum (p q M : ℕ) (hpq : p ≤ q) :
    ∑ μ : Fin M → Bool, (muNum p q μ : ℝ) = (2 * q : ℝ) ^ M := by
  unfold muNum
  have h := Finset.prod_univ_sum (fun _ : Fin M => (Finset.univ : Finset Bool))
    (fun _ b => if b then ((q + p : ℕ) : ℝ) else ((q - p : ℕ) : ℝ))
  rw [Fintype.piFinset_univ] at h
  simp only [Nat.cast_prod, Nat.cast_ite]
  rw [← h]
  simp only [Fintype.univ_bool, Finset.mem_singleton, Finset.mem_insert, Finset.sum_insert,
    Finset.sum_singleton, Bool.false_eq_true, if_true, if_false, reduceCtorEq, not_false_eq_true,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [Nat.cast_sub hpq]; push_cast; ring

theorem muWeight_eq (p q M : ℕ) (hq : 0 < q) (hpq : p ≤ q) (μ : Fin M → Bool) :
    muWeight (-(p : ℝ) / q) μ = (muNum p q μ : ℝ) / (2 * q : ℝ) ^ M := by
  unfold muWeight muNum
  push_cast
  rw [show (2 * (q : ℝ)) ^ M = ∏ _i : Fin M, (2 * (q : ℝ)) by simp, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  cases μ i <;> simp [pm, Nat.cast_sub hpq] <;> field_simp <;> ring

theorem rgVertex_inj {R : ℕ} {w w' : Fin L.nW} {r r' : Fin R} {x y : Fin L.M → Bool}
    (h : rgVertex L R w r x = rgVertex L R w' r' y) : w = w' ∧ r = r' ∧ x = y := by
  unfold rgVertex at h
  have h1 := finProdFinEquiv.injective h
  simp only [Prod.mk.injEq] at h1
  have h2 := finProdFinEquiv.injective h1.1
  simp only [Prod.mk.injEq] at h2
  exact ⟨h2.1, h2.2, (cubeEquiv L.M).injective h1.2⟩

theorem countP_rgEdges (R K p q : ℕ)
    (P : Fin (L.nW * R * 2 ^ L.M) × Fin (L.nW * R * 2 ^ L.M) → Bool) :
    (((rgEdges L R K p q).countP P : ℕ) : ℝ) =
      ∑ v, ∑ w ∈ L.nbrs v, ∑ w' ∈ L.nbrs v, ∑ r : Fin R, ∑ r' : Fin R, ∑ x, ∑ μ,
        (if rgVertex L R w r (compose x (L.σ v w)) =
            rgVertex L R w' r' (coordMul (compose x (L.σ v w')) μ) then (0 : ℝ)
        else if P (rgVertex L R w r (compose x (L.σ v w)),
            rgVertex L R w' r' (coordMul (compose x (L.σ v w')) μ)) then
          ((rgWeight L K v * muNum p q μ : ℕ) : ℝ) else 0) := by
  unfold rgEdges
  simp only [List.countP_flatMap, Function.comp_def, ← Fin.sum_univ_def, Nat.cast_sum,
    ULC.nbrs, Finset.sum_filter]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ => ?_
  by_cases hw : (v, w) ∈ L.E
  · simp only [hw, true_and, if_true]
    refine Finset.sum_congr rfl fun w' _ => ?_
    by_cases hw' : (v, w') ∈ L.E
    · simp only [hw', if_true, List.countP_flatMap, Function.comp_def, ← Fin.sum_univ_def,
        Nat.cast_sum]
      refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun r' _ => ?_
      rw [← (cubeEquiv L.M).symm.sum_comp]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← (cubeEquiv L.M).symm.sum_comp]
      refine Finset.sum_congr rfl fun μ _ => ?_
      split_ifs with h1 h2 <;> simp [List.countP_replicate, *]
    · simp [hw']
  · simp [hw]

/-- the Long Code tables read off a cut -/
def Fc (R : ℕ) (c : Fin (L.nW * R * 2 ^ L.M) → Bool) :
    Fin L.nW → Fin R → (Fin L.M → Bool) → Bool :=
  fun w r x => c (rgVertex L R w r x)

/-- weighted number of accepting tests -/
def Scut (R K p q : ℕ) (F : Fin L.nW → Fin R → (Fin L.M → Bool) → Bool) : ℝ :=
  ∑ v, ∑ w ∈ L.nbrs v, ∑ w' ∈ L.nbrs v, ∑ r : Fin R, ∑ r' : Fin R, ∑ x, ∑ μ,
    ((rgWeight L K v * muNum p q μ : ℕ) : ℝ) *
      (if F w r (compose x (L.σ v w)) ≠ F w' r' (coordMul (compose x (L.σ v w')) μ) then 1 else 0)

/-- total weight of all tests -/
def Stot (R K q : ℕ) : ℝ :=
  ∑ v, (rgWeight L K v : ℝ) * ((deg L v : ℝ) ^ 2 * ((R : ℝ) ^ 2 * ((2 : ℝ) ^ L.M * (2 * q : ℝ) ^ L.M)))

theorem Scut_nonneg (R K p q : ℕ) (F : Fin L.nW → Fin R → (Fin L.M → Bool) → Bool) :
    0 ≤ Scut (L := L) R K p q F := by
  unfold Scut
  repeat' refine Finset.sum_nonneg fun _ _ => ?_
  exact mul_nonneg (by positivity) (by split_ifs <;> norm_num)

theorem countP_cut (R K p q : ℕ) (c : Fin (L.nW * R * 2 ^ L.M) → Bool) :
    (((rgEdges L R K p q).countP (fun e => c e.1 != c e.2) : ℕ) : ℝ) =
      Scut (L := L) R K p q (Fc R c) := by
  rw [countP_rgEdges]
  unfold Scut Fc
  repeat' refine Finset.sum_congr rfl fun _ _ => ?_
  split_ifs with h1 h2 h3 h3 <;> simp_all

theorem sum_T (R K p q : ℕ) (hpq : p ≤ q) (v : Fin L.nV) :
    ∑ x : Fin L.M → Bool, ∑ μ : Fin L.M → Bool, ((rgWeight L K v * muNum p q μ : ℕ) : ℝ) =
      (rgWeight L K v : ℝ) * ((2 : ℝ) ^ L.M * (2 * q : ℝ) ^ L.M) := by
  simp only [Nat.cast_mul, ← Finset.mul_sum, sum_muNum p q L.M hpq, Finset.sum_const,
    Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
  push_cast; ring

theorem length_le (R K p q : ℕ) (hpq : p ≤ q) :
    (((rgEdges L R K p q).length : ℕ) : ℝ) ≤ Stot (L := L) R K q ∧
      (R : ℝ) * (Stot (L := L) R K q - (((rgEdges L R K p q).length : ℕ) : ℝ)) ≤
        Stot (L := L) R K q := by
  have hlen := countP_rgEdges (L := L) R K p q (fun _ => true)
  rw [List.countP_true] at hlen
  rw [hlen]
  -- the full sum
  have hfull : Stot (L := L) R K q = ∑ v, ∑ w ∈ L.nbrs v, ∑ w' ∈ L.nbrs v, ∑ r : Fin R,
      ∑ r' : Fin R, ∑ x : Fin L.M → Bool, ∑ μ : Fin L.M → Bool,
        ((rgWeight L K v * muNum p q μ : ℕ) : ℝ) := by
    unfold Stot
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [sum_T R K p q hpq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    unfold deg; ring
  rw [hfull]
  simp only [↓reduceIte]
  constructor
  · repeat' refine Finset.sum_le_sum fun _ _ => ?_
    split_ifs
    · positivity
    · exact le_rfl
  · -- the loop part
    set C : Fin L.nV → ℝ := fun v => (rgWeight L K v : ℝ) * ((2 : ℝ) ^ L.M * (2 * q : ℝ) ^ L.M)
      with hC
    have hterm : ∀ v w w' (r r' : Fin R), ∑ x : Fin L.M → Bool, ∑ μ : Fin L.M → Bool,
        (((rgWeight L K v * muNum p q μ : ℕ) : ℝ) -
          (if rgVertex L R w r (compose x (L.σ v w)) =
            rgVertex L R w' r' (coordMul (compose x (L.σ v w')) μ) then (0 : ℝ)
            else ((rgWeight L K v * muNum p q μ : ℕ) : ℝ))) ≤
        if w' = w then (if r' = r then C v else 0) else 0 := by
      intro v w w' r r'
      by_cases hw : w' = w
      · by_cases hr : r' = r
        · simp only [hw, hr, if_true]
          simp only [hC]
          rw [← sum_T R K p q hpq v]
          refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun μ _ => ?_
          split_ifs
          · simp
          · simp only [sub_self]; positivity
        · simp only [hr, if_false, hw, if_true]
          apply le_of_eq
          refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun μ _ => ?_
          rw [if_neg]; · simp
          intro h; exact hr (rgVertex_inj h).2.1.symm
      · simp only [hw, if_false]
        apply le_of_eq
        refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun μ _ => ?_
        rw [if_neg]; · simp
        intro h; exact hw (rgVertex_inj h).1.symm
    have hv : ∀ v, ∑ w ∈ L.nbrs v, ∑ w' ∈ L.nbrs v, ∑ r : Fin R, ∑ r' : Fin R,
        ∑ x : Fin L.M → Bool, ∑ μ : Fin L.M → Bool,
        (((rgWeight L K v * muNum p q μ : ℕ) : ℝ) -
          (if rgVertex L R w r (compose x (L.σ v w)) =
            rgVertex L R w' r' (coordMul (compose x (L.σ v w')) μ) then (0 : ℝ)
            else ((rgWeight L K v * muNum p q μ : ℕ) : ℝ))) ≤
        (deg L v : ℝ) * ((R : ℝ) * C v) := by
      intro v
      calc _ ≤ ∑ w ∈ L.nbrs v, ∑ w' ∈ L.nbrs v, ∑ r : Fin R, ∑ r' : Fin R,
            (if w' = w then (if r' = r then C v else 0) else 0) :=
            Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun w' _ =>
              Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun r' _ => hterm v w w' r r'
        _ = ∑ w ∈ L.nbrs v, ∑ _r : Fin R, C v := by
            refine Finset.sum_congr rfl fun w hw => ?_
            rw [Finset.sum_congr rfl (fun w' _ => show ∑ r : Fin R, ∑ r' : Fin R,
                (if w' = w then (if r' = r then C v else 0) else 0) =
                if w' = w then ∑ r : Fin R, ∑ r' : Fin R, (if r' = r then C v else 0) else 0 by
                  split_ifs <;> simp)]
            rw [Finset.sum_ite_eq' _ w, if_pos hw]
            simp
        _ = _ := by simp [deg]
    have hAv : ∀ v, ∑ w ∈ L.nbrs v, ∑ w' ∈ L.nbrs v, ∑ r : Fin R,
      ∑ r' : Fin R, ∑ x : Fin L.M → Bool, ∑ μ : Fin L.M → Bool,
        ((rgWeight L K v * muNum p q μ : ℕ) : ℝ) = (rgWeight L K v : ℝ) * ((deg L v : ℝ) ^ 2 *
          ((R : ℝ) ^ 2 * ((2 : ℝ) ^ L.M * (2 * q : ℝ) ^ L.M))) := by
      intro v
      simp only [sum_T R K p q hpq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      unfold deg; ring
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun v _ => ?_
    have h1 := hv v
    simp only [← Finset.sum_sub_distrib] at h1 ⊢
    have hd : (deg L v : ℝ) ≤ (deg L v : ℝ) ^ 2 := by
      have := Nat.le_mul_self (deg L v); rw [sq]; exact_mod_cast this
    have hR0 : (0 : ℝ) ≤ R := by positivity
    have hC0 : 0 ≤ C v := by simp only [hC]; positivity
    calc (R : ℝ) * _ ≤ (R : ℝ) * ((deg L v : ℝ) * ((R : ℝ) * C v)) :=
          mul_le_mul_of_nonneg_left h1 hR0
      _ ≤ (R : ℝ) * ((deg L v : ℝ) ^ 2 * ((R : ℝ) * C v)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hd (by positivity)) hR0
      _ = _ := by rw [hAv]; simp only [hC]; ring

theorem Stot_eq (R K q : ℕ) : Stot (L := L) R K q =
    (Fintype.card (Cop L K) : ℝ) * ((R : ℝ) ^ 2 * ((2 : ℝ) ^ L.M * (2 * q : ℝ) ^ L.M)) := by
  rw [card_Cop_eq, Finset.sum_mul]
  unfold Stot
  refine Finset.sum_congr rfl fun v _ => ?_
  push_cast; ring

theorem accProb_eq (R K p q : ℕ) (hR : 0 < R) (hq : 0 < q) (hpq : p ≤ q)
    (F : Fin L.nW → Fin R → (Fin L.M → Bool) → Bool) :
    accProb (Lpp L R K) (-(p : ℝ) / q) (Fpp R K F) =
      Scut (L := L) R K p q F / Stot (L := L) R K q := by
  have hmw : ∀ μ : Fin L.M → Bool, muWeight (-(p : ℝ) / q) μ =
      (muNum p q μ : ℝ) / (2 * q : ℝ) ^ L.M := muWeight_eq p q L.M hq hpq
  rw [accProb_Lpp R K hR, Stot_eq]
  unfold accT Scut
  simp only [hmw]
  rw [div_eq_mul_inv _ (_ * _)]
  simp only [Finset.mul_sum, Finset.sum_mul]
  repeat' refine Finset.sum_congr rfl fun _ _ => ?_
  have h2 : (2 : ℝ) ^ L.M ≠ 0 := by positivity
  have hq' : (2 * (q : ℝ)) ^ L.M ≠ 0 := by
    have : (0 : ℝ) < q := by exact_mod_cast hq
    positivity
  have hR' : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
  push_cast
  field_simp

end

end OptInapprox.MaxCut.MCX


namespace OptInapprox.MaxCut.MCX

open Finset

noncomputable section

variable {L : ULC}

theorem Stot_pos (R K q : ℕ) (hR : 0 < R) (hK : 0 < K) (hq : 0 < q) (hE : L.E.Nonempty) :
    0 < Stot (L := L) R K q := by
  rw [Stot_eq]
  have h1 : (0 : ℝ) < Fintype.card (Cop L K) := by exact_mod_cast card_Cop_pos K hK hE
  have h2 : (0 : ℝ) < R := by exact_mod_cast hR
  have h3 : (0 : ℝ) < q := by exact_mod_cast hq
  positivity

theorem cut_bounds (R p q : ℕ) (hR : 2 ≤ R) (hq : 0 < q) (hpq : p ≤ q) (hE : L.E.Nonempty)
    (c : Fin (L.nW * R * 2 ^ L.M) → Bool) :
    (reductionGraph L R 2 p q).edges ≠ [] ∧
    accProb (Lpp L R 2) (-(p : ℝ) / q) (Fpp R 2 (Fc R c)) ≤
      (reductionGraph L R 2 p q).cutFrac c ∧
    (reductionGraph L R 2 p q).cutFrac c * (1 - 1 / (R : ℝ)) ≤
      accProb (Lpp L R 2) (-(p : ℝ) / q) (Fpp R 2 (Fc R c)) := by
  have hR0 : 0 < R := by omega
  rw [accProb_eq R 2 p q hR0 hq hpq]
  obtain ⟨hle, hge⟩ := length_le (L := L) R 2 p q hpq
  have hS := Stot_pos (L := L) R 2 q hR0 (by norm_num) hq hE
  have hRr : (2 : ℝ) ≤ R := by exact_mod_cast hR
  set len : ℝ := (((rgEdges L R 2 p q).length : ℕ) : ℝ) with hlen
  set S := Stot (L := L) R 2 q
  have hlen_lb : (1 - 1 / (R : ℝ)) * S ≤ len := by
    have : S - len ≤ S / R := by rw [le_div_iff₀ (by linarith)]; linarith
    have h' : (1 - 1 / (R : ℝ)) * S = S - S / R := by ring
    linarith
  have hlenpos : 0 < len := by
    have : 0 < (1 - 1 / (R : ℝ)) * S := by
      apply mul_pos _ hS
      rw [sub_pos, div_lt_one (by linarith)]; linarith
    linarith
  have hcut : (reductionGraph L R 2 p q).cutFrac c = Scut (L := L) R 2 p q (Fc R c) / len := by
    unfold WMaxCut.cutFrac
    rw [hlen, ← countP_cut]
    rfl
  have hSc := Scut_nonneg (L := L) R 2 p q (Fc R c)
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have : len = 0 := by rw [hlen]; simp [reductionGraph] at h; simp [h]
    linarith
  · rw [hcut]
    exact div_le_div_of_nonneg_left hSc hlenpos hle
  · rw [hcut, div_mul_eq_mul_div, div_le_div_iff₀ hlenpos hS]
    calc Scut (L := L) R 2 p q (Fc R c) * (1 - 1 / (R : ℝ)) * S
        = Scut (L := L) R 2 p q (Fc R c) * ((1 - 1 / (R : ℝ)) * S) := by ring
      _ ≤ Scut (L := L) R 2 p q (Fc R c) * len := mul_le_mul_of_nonneg_left hlen_lb hSc

end

end OptInapprox.MaxCut.MCX

open OptInapprox.MaxCut OptInapprox.MaxCut.MCX in
theorem solution (hUGC : UGC) (hMIS : MajorityIsStablest) (ρ ε : ℝ) (hρ₁ : -1 < ρ)
    (hρ₂ : ρ < 0) (hε : 0 < ε) :
    GapNPHard encMaxCut
      (fun G : WMaxCut => G.edges ≠ [] ∧ ∃ c, 1 / 2 - ρ / 2 ≤ G.cutFrac c)
      (fun G : WMaxCut => G.edges ≠ [] ∧ ∀ c, G.cutFrac c ≤ Real.arccos ρ / Real.pi + ε) := by
  set ε₀ := min ε 1 with hε₀_def
  have hε₀ : 0 < ε₀ := lt_min hε one_pos
  have hε₀1 : ε₀ ≤ 1 := min_le_right _ _
  have hε₀ε : ε₀ ≤ ε := min_le_left _ _
  have hπ := Real.pi_pos
  -- a rational `ρ' < ρ` close to `ρ`
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.1 (Real.continuous_arccos.continuousAt (x := ρ))
    (Real.pi * ε₀ / 4) (by positivity)
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (max_lt (by linarith : ρ - δ < ρ) hρ₁)
  set ρ' : ℝ := (r : ℝ) with hρ'_def
  have hρ'1 : -1 < ρ' := lt_of_le_of_lt (le_max_right _ _) hr1
  have hρ'δ : ρ - δ < ρ' := lt_of_le_of_lt (le_max_left _ _) hr1
  have hρ'2 : ρ' < 0 := by linarith
  have hA' : Real.arccos ρ' / Real.pi ≤ Real.arccos ρ / Real.pi + ε₀ / 4 := by
    have h := hcont (x := ρ') (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    rw [Real.dist_eq, abs_lt] at h
    rw [div_le_iff₀ hπ, add_mul, div_mul_cancel₀ _ hπ.ne']
    linarith [h.2]
  -- write `ρ' = -p/q`
  set p : ℕ := (-r.num).toNat with hp_def
  set q : ℕ := r.den with hq_def
  have hq : 0 < q := r.den_pos
  have hnum : r.num < 0 := Rat.num_neg.2 (by have h0 : (r : ℝ) < 0 := hρ'2; exact_mod_cast h0)
  have hpR : (p : ℝ) = -(r.num : ℝ) := by
    rw [hp_def]
    have : ((-r.num).toNat : ℤ) = -r.num := Int.toNat_of_nonneg (by omega)
    have h2 : (((-r.num).toNat : ℕ) : ℝ) = (((-r.num).toNat : ℤ) : ℝ) := rfl
    rw [h2, this]; push_cast; ring
  have hρ'eq : ρ' = -(p : ℝ) / q := by
    rw [hpR, hρ'_def, Rat.cast_def]; ring
  have hpq : p ≤ q := by
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have : (p : ℝ) < q := by
      have h1 : -1 < -(p : ℝ) / q := hρ'eq ▸ hρ'1
      rw [lt_div_iff₀ hqR] at h1; linarith
    exact_mod_cast this.le
  -- completeness slack
  set η : ℝ := (ρ - ρ') / (8 * (1 - ρ')) with hη_def
  have h1ρ' : 0 < 1 - ρ' := by linarith
  have hη : 0 < η := by rw [hη_def]; apply div_pos <;> linarith
  have hcomp : 1 / 2 - ρ / 2 ≤ (1 - 2 * (2 * η)) * (1 / 2 - ρ' / 2) := by
    rw [hη_def]
    have : (1 - 2 * (2 * ((ρ - ρ') / (8 * (1 - ρ'))))) * (1 / 2 - ρ' / 2) =
        1 / 2 - ρ' / 2 - (ρ - ρ') / 4 := by field_simp; ring
    rw [this]; linarith
  -- soundness constant
  obtain ⟨γ', hγ', hsound⟩ := soundness_8_3 hMIS ρ' hρ'1 hρ'2 (ε₀ / 2) (by linarith)
  obtain ⟨M₀, hM₀⟩ := hUGC η (γ' / 4) hη (by linarith)
  -- copies
  set R : ℕ := ⌈8 / ε₀⌉₊ + 2 with hR_def
  have hR2 : 2 ≤ R := by omega
  have hRε : 1 / (R : ℝ) ≤ ε₀ / 8 := by
    have h1 : 8 / ε₀ ≤ (⌈8 / ε₀⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (R : ℝ) = (⌈8 / ε₀⌉₊ : ℝ) + 2 := by rw [hR_def]; push_cast; ring
    have hRpos : (0 : ℝ) < R := by rw [h2]; positivity
    rw [div_le_iff₀ hRpos]
    have : 8 ≤ ε₀ * R := by
      rw [h2]
      have := (div_le_iff₀ hε₀).1 h1
      nlinarith
    linarith
  obtain ⟨g, hg, hgenc⟩ := reductionGraph_polyTime M₀ R 2 p q
  have hRed := SetCoverThreshold.SetCover.gapNPHard_of_reduction encULC
    (fun L : ULC => L.M = M₀ ∧ L.E.Nonempty ∧ 1 - η ≤ L.OPT)
    (fun L : ULC => L.M = M₀ ∧ L.E.Nonempty ∧ L.OPT ≤ γ' / 4) encMaxCut
    (fun G : WMaxCut => G.edges ≠ [] ∧ ∃ c, 1 / 2 - ρ / 2 ≤ G.cutFrac c)
    (fun G : WMaxCut => G.edges ≠ [] ∧ ∀ c, G.cutFrac c ≤ Real.arccos ρ / Real.pi + ε)
    hM₀ (fun L => reductionGraph L R 2 p q) g hg
    (fun L hL => (hgenc L (by rcases hL with h | h <;> exact h.1)).symm) ?_ ?_
  · exact hRed
  · -- completeness
    rintro L ⟨-, hE, hopt⟩
    have hne : Nonempty ((Fin L.nV → Fin L.M) × (Fin L.nW → Fin L.M)) := by
      by_contra hc
      rw [not_nonempty_iff] at hc
      have : L.OPT = 0 := Real.iSup_of_isEmpty _
      have hη1 : η < 1 := by
        rw [hη_def, div_lt_one (by linarith)]; linarith
      linarith
    obtain ⟨lab, hlab⟩ := exists_eq_ciSup_of_finite (f := L.satFrac)
    have hlab' : L.satFrac lab = L.OPT := hlab
    have h1 := satFrac_lift R (by omega) hE lab
    have h3 := completeness_8_2 (Lpp L R 2) (Lpp_regular R 2 (by omega) (by norm_num) hE) ρ'
      hρ'1 hρ'2 (2 * η) (liftLab R 2 lab) (by linarith)
    let c : Fin (L.nW * R * 2 ^ L.M) → Bool := fun u =>
      ((cubeEquiv L.M).symm (finProdFinEquiv.symm u).2)
        (lab.2 (finProdFinEquiv.symm (finProdFinEquiv.symm u).1).1)
    have hF : Fpp R 2 (Fc R c) = fun w => longCode ((liftLab R 2 lab).2 w) := by
      funext b x
      simp only [Fpp, Fc, c, rgVertex, Equiv.symm_apply_apply, longCode, liftLab]
    obtain ⟨hne', hlo, -⟩ := cut_bounds R p q hR2 hq hpq hE c
    refine ⟨hne', c, ?_⟩
    rw [← hρ'eq, hF] at hlo
    linarith
  · -- soundness
    rintro L ⟨-, hE, hopt⟩
    refine ⟨(cut_bounds R p q hR2 hq hpq hE (fun _ => false)).1, fun c => ?_⟩
    by_contra hlt
    push Not at hlt
    obtain ⟨-, -, hup⟩ := cut_bounds R p q hR2 hq hpq hE c
    rw [← hρ'eq] at hup
    have hA1 : Real.arccos ρ / Real.pi ≤ 1 := by
      rw [div_le_one hπ]; exact Real.arccos_le_pi _
    have hA0 : 0 ≤ Real.arccos ρ / Real.pi := div_nonneg (Real.arccos_nonneg _) hπ.le
    set A := Real.arccos ρ / Real.pi
    set cf := (reductionGraph L R 2 p q).cutFrac c
    have hRpos : (0 : ℝ) < 1 / R := by
      have : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
      positivity
    have hR1 : 1 / (R : ℝ) < 1 := by linarith
    have hacc : Real.arccos ρ' / Real.pi + ε₀ / 2 ≤
        accProb (Lpp L R 2) ρ' (Fpp R 2 (Fc R c)) := by
      have e1 : (A + ε₀) * (1 - 1 / R) ≤ cf * (1 - 1 / R) :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      have e2 : (A + ε₀) * (1 / R) ≤ 2 * (ε₀ / 8) :=
        mul_le_mul (by linarith) hRε hRpos.le (by norm_num)
      nlinarith
    have hγ := hsound (Lpp L R 2) (Lpp_regular R 2 (by omega) (by norm_num) hE)
      (Fpp R 2 (Fc R c)) hacc
    have hOPT : (Lpp L R 2).OPT ≤ 2 * L.OPT :=
      Real.iSup_le (fun lab => satFrac_Lpp_le R (by omega) hE lab)
        (by linarith [OPT_nonneg L])
    linarith
