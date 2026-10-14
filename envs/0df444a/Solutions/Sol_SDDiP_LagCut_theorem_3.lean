-- Prove2me | solution 1 for SDDiP.LagCut.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:28:03.318524+00:00
-- url     : https://prove2.me/submissions/b01f6dbb-8f8d-40fe-a998-cc5e598b69f0

import Mathlib
import Definitions.Def_SDDiP_LagCut_Node

namespace RRAux_SDDiP_LagCut_theorem_3

open SDDiP.LagCut SDDiP.LagCut.Node

variable {d l : ℕ}

abbrev Q (d l : ℕ) := (Fin d → ℝ) × (Fin d → ℝ) × (Fin l → ℝ) × ℝ

lemma cont_dot {α : Type*} [TopologicalSpace α] (c : Fin d → ℝ) {g : α → Fin d → ℝ}
    (hg : Continuous g) : Continuous fun a => c ⬝ᵥ g a := by
  unfold dotProduct
  exact continuous_finsetSum _ fun i _ => continuous_const.mul ((continuous_apply i).comp hg)

lemma psi_set_nonempty (N : Node d l) (x : Fin d → ℝ) :
    ({θ : ℝ | N.L ≤ θ ∧ ∀ ℓ, N.cut ℓ x ≤ θ}).Nonempty := by
  refine ⟨|N.L| + ∑ ℓ, |N.cut ℓ x|, ?_, ?_⟩
  · have := Finset.sum_nonneg (fun ℓ (_ : ℓ ∈ Finset.univ) => abs_nonneg (N.cut ℓ x))
    linarith [le_abs_self N.L]
  · intro ℓ
    have h1 := Finset.single_le_sum (f := fun ℓ => |N.cut ℓ x|) (fun ℓ _ => abs_nonneg _)
      (Finset.mem_univ ℓ)
    have h2 := le_abs_self (N.cut ℓ x)
    have h3 := abs_nonneg N.L
    linarith

lemma psi_ge (N : Node d l) (x : Fin d → ℝ) : N.L ≤ N.ψ x ∧ ∀ ℓ, N.cut ℓ x ≤ N.ψ x :=
  ⟨le_csInf (psi_set_nonempty N x) (fun _ h => h.1),
    fun ℓ => le_csInf (psi_set_nonempty N x) (fun _ h => h.2 ℓ)⟩

lemma psi_le (N : Node d l) (x : Fin d → ℝ) (θ : ℝ) (h1 : N.L ≤ θ) (h2 : ∀ ℓ, N.cut ℓ x ≤ θ) :
    N.ψ x ≤ θ :=
  csInf_le ⟨N.L, fun _ ht => ht.1⟩ ⟨h1, h2⟩

lemma lower (N : Node d l) (π : Fin d → ℝ) :
    ∃ b, ∀ w ∈ N.X, b ≤ N.f w.2.1 w.2.2 - π ⬝ᵥ w.1 := by
  have hc : Continuous fun w : (Fin d → ℝ) × (Fin d → ℝ) × (Fin l → ℝ) =>
      N.f w.2.1 w.2.2 - π ⬝ᵥ w.1 := by
    unfold Node.f
    exact ((cont_dot _ (continuous_fst.comp continuous_snd)).add
      (cont_dot _ (continuous_snd.comp continuous_snd))).sub (cont_dot _ continuous_fst)
  obtain ⟨b, hb⟩ := (N.X_compact.image hc).bddBelow
  exact ⟨b, fun w hw => hb ⟨w, hw, rfl⟩⟩

lemma lag_bdd (N : Node d l) (π : Fin d → ℝ) : BddBelow (N.lagValues π) := by
  obtain ⟨b, hb⟩ := lower N π
  refine ⟨b + N.L, ?_⟩
  rintro s ⟨p, hp, rfl⟩
  have h1 : b ≤ N.f p.2.1 p.2.2.1 - π ⬝ᵥ p.1 := hb _ hp.1.1
  have h2 : N.L ≤ p.2.2.2 := hp.2.1
  show b + N.L ≤ N.f p.2.1 p.2.2.1 + p.2.2.2 - π ⬝ᵥ p.1
  linarith

lemma lag_le (N : Node d l) (π : Fin d → ℝ) (p : Q d l) (hp : p ∈ N.X'') :
    N.lag π ≤ N.f p.2.1 p.2.2.1 + p.2.2.2 - π ⬝ᵥ p.1 :=
  csInf_le (lag_bdd N π) ⟨p, hp, rfl⟩

lemma X''_nonempty (N : Node d l) (hX' : N.X'.Nonempty) : N.X''.Nonempty := by
  obtain ⟨w, hw⟩ := hX'
  exact ⟨(w.1, w.2.1, w.2.2, N.ψ w.2.1), hw, (psi_ge N _).1, (psi_ge N _).2⟩

lemma one_div_le_one (n : ℕ) : (1 : ℝ) / (n + 1) ≤ 1 := by
  rw [div_le_one (by positivity)]
  linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

lemma one_div_anti {n m : ℕ} (h : n ≤ m) : (1 : ℝ) / (m + 1) ≤ 1 / (n + 1) := by
  apply one_div_le_one_div_of_le (by positivity)
  have : (n : ℝ) ≤ m := by exact_mod_cast h
  linarith

lemma term_nonneg (a z : ℝ) (ha : a = 0 ∨ a = 1) (hz : 0 ≤ z ∧ z ≤ 1) :
    0 ≤ (2 * a - 1) * (a - z) := by
  rcases ha with rfl | rfl <;> nlinarith [hz.1, hz.2]

lemma term_zero (a z : ℝ) (ha : a = 0 ∨ a = 1) (h : (2 * a - 1) * (a - z) = 0) : z = a := by
  rcases ha with rfl | rfl
  · linarith
  · linarith

lemma pen_ident (n : ℕ) (xhat z : Fin d → ℝ) :
    (fun j => (n : ℝ) * (2 * xhat j - 1)) ⬝ᵥ xhat - (fun j => (n : ℝ) * (2 * xhat j - 1)) ⬝ᵥ z
      = n * ∑ j, (2 * xhat j - 1) * (xhat j - z j) := by
  unfold dotProduct
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma arch (a D V : ℝ) (hD : 0 ≤ D) (h : ∀ n : ℕ, a + n * D ≤ V + 1 / (n + 1)) :
    D = 0 ∧ a ≤ V := by
  constructor
  · by_contra hne
    have hpos : 0 < D := lt_of_le_of_ne hD (Ne.symm hne)
    obtain ⟨n, hn⟩ := exists_nat_gt ((V + 1 - a) / D)
    have h1 := (div_lt_iff₀ hpos).mp hn
    have h2 := h n
    have h3 := one_div_le_one n
    linarith
  · apply le_of_forall_pos_lt_add
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    have h2 := h n
    have h3 : 0 ≤ (n : ℝ) * D := mul_nonneg n.cast_nonneg hD
    linarith

lemma cut_cont (N : Node d l) (ℓ : Fin N.i) : Continuous fun p : Q d l => N.cut ℓ p.2.1 := by
  unfold Node.cut
  exact continuous_finsetSum _ fun m _ => continuous_const.mul
    (continuous_const.add (cont_dot _ (continuous_fst.comp continuous_snd)))

theorem tight (N : Node d l) (xhat : Fin d → ℝ) (hxhat : IsBinary xhat)
    (hX' : N.X'.Nonempty) (πhat : Fin d → ℝ) (hopt : N.IsDualOptimal xhat πhat) :
    IsLeast (N.fwdValues xhat) (N.lag πhat + πhat ⬝ᵥ xhat) := by
  obtain ⟨V, hV⟩ : ∃ V, V = N.lag πhat + πhat ⬝ᵥ xhat := ⟨_, rfl⟩
  rw [← hV]
  have hweak : ∀ t ∈ N.fwdValues xhat, V ≤ t := by
    rintro t ⟨x, y, hXb, hxb, rfl⟩
    have hp : ((xhat, x, y, N.ψ x) : Q d l) ∈ N.X'' :=
      ⟨⟨hXb.1, hxb, hXb.2⟩, (psi_ge N x).1, (psi_ge N x).2⟩
    have h1 : N.lag πhat ≤ N.f x y + N.ψ x - πhat ⬝ᵥ xhat := lag_le N πhat _ hp
    rw [hV]; linarith
  refine ⟨?_, hweak⟩
  obtain ⟨b0, hb0⟩ := lower N 0
  let T : ℝ := V + 1 - b0
  let D : Q d l → ℝ := fun p => ∑ j, (2 * xhat j - 1) * (xhat j - p.1 j)
  have hDnn : ∀ p : Q d l, InUnitBox p.1 → 0 ≤ D p := fun p hp =>
    Finset.sum_nonneg fun j _ => term_nonneg _ _ (hxhat j) (hp j)
  have hD0 : ∀ p : Q d l, InUnitBox p.1 → D p = 0 → p.1 = xhat := by
    intro p hp h0
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => term_nonneg _ _ (hxhat j) (hp j))).mp h0
    funext j
    exact term_zero _ _ (hxhat j) (this j (Finset.mem_univ j))
  let obj : Q d l → ℝ := fun p => N.f p.2.1 p.2.2.1 + p.2.2.2
  have hobjc : Continuous obj := by
    show Continuous fun p : Q d l => N.c ⬝ᵥ p.2.1 + N.e ⬝ᵥ p.2.2.1 + p.2.2.2
    exact ((cont_dot _ (continuous_fst.comp continuous_snd)).add
      (cont_dot _ (continuous_fst.comp (continuous_snd.comp continuous_snd)))).add
      (continuous_snd.comp (continuous_snd.comp continuous_snd))
  have hDc : Continuous D := continuous_finsetSum _ fun j _ => continuous_const.mul
    (continuous_const.sub ((continuous_apply j).comp continuous_fst))
  let K : Set (Q d l) := {p | (p.1, p.2.1, p.2.2.1) ∈ N.X} ∩ {p | IsBinary p.2.1} ∩
    {p | InUnitBox p.1} ∩ {p | N.L ≤ p.2.2.2} ∩ {p | ∀ ℓ, N.cut ℓ p.2.1 ≤ p.2.2.2} ∩
    {p | p.2.2.2 ≤ T}
  have hKcl : IsClosed K := by
    refine IsClosed.inter (IsClosed.inter (IsClosed.inter (IsClosed.inter
      (IsClosed.inter ?_ ?_) ?_) ?_) ?_) ?_
    · exact N.X_compact.isClosed.preimage (by fun_prop)
    · show IsClosed {p : Q d l | ∀ j, p.2.1 j = 0 ∨ p.2.1 j = 1}
      simp only [Set.ofPred_forall, Set.ofPred_or]
      exact isClosed_iInter fun j => (isClosed_eq (by fun_prop) (by fun_prop)).union
        (isClosed_eq (by fun_prop) (by fun_prop))
    · show IsClosed {p : Q d l | ∀ j, 0 ≤ p.1 j ∧ p.1 j ≤ 1}
      simp only [Set.ofPred_forall, Set.ofPred_and]
      exact isClosed_iInter fun j => (isClosed_le (by fun_prop) (by fun_prop)).inter
        (isClosed_le (by fun_prop) (by fun_prop))
    · exact isClosed_le (by fun_prop) (by fun_prop)
    · simp only [Set.ofPred_forall]
      exact isClosed_iInter fun ℓ => isClosed_le (cut_cont N ℓ) (by fun_prop)
    · exact isClosed_le (by fun_prop) (by fun_prop)
  have hKc : IsCompact K := by
    have hE : IsCompact ((fun q : ((Fin d → ℝ) × (Fin d → ℝ) × (Fin l → ℝ)) × ℝ =>
        ((q.1.1, q.1.2.1, q.1.2.2, q.2) : Q d l)) '' (N.X ×ˢ Set.Icc N.L T)) :=
      (N.X_compact.prod isCompact_Icc).image (by fun_prop)
    refine hE.of_isClosed_subset hKcl ?_
    rintro p ⟨⟨⟨⟨⟨h1, _⟩, _⟩, h4⟩, _⟩, h6⟩
    exact ⟨((p.1, p.2.1, p.2.2.1), p.2.2.2), ⟨h1, h4, h6⟩, rfl⟩
  let C : ℕ → Set (Q d l) := fun n => K ∩ {p | obj p + n * D p ≤ V + 1 / (n + 1)}
  have hCcl : ∀ n, IsClosed (C n) := fun n =>
    hKcl.inter (isClosed_le (hobjc.add (continuous_const.mul hDc)) continuous_const)
  have hCsub : ∀ n, C (n + 1) ⊆ C n := by
    rintro n p ⟨hpK, hp⟩
    refine ⟨hpK, ?_⟩
    have hd := hDnn p hpK.1.1.1.2
    have h1 : (n : ℝ) * D p ≤ ((n + 1 : ℕ) : ℝ) * D p :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ n) hd
    have h2 := one_div_anti (Nat.le_succ n)
    have hp' : obj p + ((n + 1 : ℕ) : ℝ) * D p ≤ V + 1 / (((n + 1 : ℕ) : ℝ) + 1) := hp
    show obj p + n * D p ≤ V + 1 / (n + 1)
    linarith
  have hCne : ∀ n, (C n).Nonempty := by
    intro n
    let πn : Fin d → ℝ := fun j => (n : ℝ) * (2 * xhat j - 1)
    have hle : N.lag πn + πn ⬝ᵥ xhat ≤ V := by rw [hV]; exact hopt πn
    have hne : (N.lagValues πn).Nonempty := (X''_nonempty N hX').image _
    have hlt : N.lag πn < N.lag πn + 1 / (n + 1) := by
      have : (0 : ℝ) < 1 / (n + 1) := by positivity
      linarith
    obtain ⟨s, ⟨p, hp, rfl⟩, hs⟩ := exists_lt_of_csInf_lt hne hlt
    have hs' : N.f p.2.1 p.2.2.1 + p.2.2.2 - πn ⬝ᵥ p.1 < N.lag πn + 1 / (n + 1) := hs
    have hid := pen_ident n xhat p.1
    have hmain : obj p + n * D p < V + 1 / (n + 1) := by
      show N.f p.2.1 p.2.2.1 + p.2.2.2 + n * D p < V + 1 / (n + 1)
      have : D p = ∑ j, (2 * xhat j - 1) * (xhat j - p.1 j) := rfl
      rw [this, ← hid]
      linarith
    have hbox : InUnitBox p.1 := hp.1.2.2
    have hd := mul_nonneg (n.cast_nonneg : (0 : ℝ) ≤ n) (hDnn p hbox)
    have hb : b0 ≤ N.f p.2.1 p.2.2.1 - (0 : Fin d → ℝ) ⬝ᵥ p.1 := hb0 _ hp.1.1
    rw [zero_dotProduct, sub_zero] at hb
    have h1 := one_div_le_one n
    have hT : p.2.2.2 ≤ T := by
      show p.2.2.2 ≤ V + 1 - b0
      have : obj p = N.f p.2.1 p.2.2.1 + p.2.2.2 := rfl
      linarith
    exact ⟨p, ⟨⟨⟨⟨⟨hp.1.1, hp.1.2.1⟩, hbox⟩, hp.2.1⟩, hp.2.2⟩, hT⟩, hmain.le⟩
  obtain ⟨p, hp⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hCsub
    hCne (hKc.of_isClosed_subset (hCcl 0) Set.inter_subset_left) hCcl
  rw [Set.mem_iInter] at hp
  have hpK : p ∈ K := (hp 0).1
  obtain ⟨⟨⟨⟨⟨hX, hbin⟩, hbox⟩, hL⟩, hcut⟩, _⟩ := hpK
  obtain ⟨hD, hobj⟩ := arch (obj p) (D p) V (hDnn p hbox) (fun n => (hp n).2)
  have hz : p.1 = xhat := hD0 p hbox hD
  have hψ := psi_le N p.2.1 p.2.2.2 hL hcut
  have hmem : N.f p.2.1 p.2.2.1 + N.ψ p.2.1 ∈ N.fwdValues xhat :=
    ⟨p.2.1, p.2.2.1, ⟨hz ▸ hX, hz ▸ hbox⟩, hbin, rfl⟩
  have hw := hweak _ hmem
  have hobj' : N.f p.2.1 p.2.2.1 + p.2.2.2 ≤ V := hobj
  have : V = N.f p.2.1 p.2.2.1 + N.ψ p.2.1 := by linarith
  rw [this]; exact hmem

end RRAux_SDDiP_LagCut_theorem_3

open SDDiP.LagCut in
open Node in
theorem solution {d l : ℕ} (N : Node d l) (xhat : Fin d → ℝ) (hxhat : IsBinary xhat)
    (hX' : N.X'.Nonempty) (πhat : Fin d → ℝ) (hopt : N.IsDualOptimal xhat πhat)
    (Qc : Fin N.nC → (Fin d → ℝ) → ℝ)
    (hcuts : ∀ (ℓ : Fin N.i) (m : Fin N.nC) (x : Fin d → ℝ), IsBinary x →
      N.v ℓ m + N.π ℓ m ⬝ᵥ x ≤ Qc m x)
    (hL : ∀ x : Fin d → ℝ, IsBinary x → N.L ≤ N.expCostToGo Qc x) :
    (IsLeast (N.fwdValues xhat) (N.lag πhat + πhat ⬝ᵥ xhat) ∧
        N.fwdValue xhat = N.lag πhat + πhat ⬝ᵥ xhat) ∧
      ∀ xa : Fin d → ℝ, IsBinary xa →
        N.lag πhat + πhat ⬝ᵥ xa ∈ lowerBounds (N.trueValues (N.expCostToGo Qc) xa) := by
  have ht := RRAux_SDDiP_LagCut_theorem_3.tight N xhat hxhat hX' πhat hopt
  refine ⟨⟨ht, ht.csInf_eq⟩, ?_⟩
  rintro xa hxa t ⟨x, y, hXb, hxb, rfl⟩
  have hc : ∀ ℓ, N.cut ℓ x ≤ N.expCostToGo Qc x := fun ℓ =>
    Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left (hcuts ℓ m x hxb) (N.q_nonneg m)
  have hp : ((xa, x, y, N.expCostToGo Qc x) : RRAux_SDDiP_LagCut_theorem_3.Q d l) ∈ N.X'' :=
    ⟨⟨hXb.1, hxb, hXb.2⟩, hL x hxb, hc⟩
  have h1 : N.lag πhat ≤ N.f x y + N.expCostToGo Qc x - πhat ⬝ᵥ xa :=
    RRAux_SDDiP_LagCut_theorem_3.lag_le N πhat _ hp
  linarith

#print axioms solution
