-- Prove2me | solution 1 for SingleExpBisect.Main.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T09:19:27.791995+00:00
-- url     : https://prove2.me/submissions/8de9900b-60a6-47a7-bf0f-cb21591cb701

/- The cut-edge membership, minimum bound and attainment lemmas are adapted from Secousses, Prove2Me submission 797eedb1-a223-4590-b528-4b3d16d0ab3c (Apache-2.0). -/
import Mathlib
import Definitions.Def_MinBisectFPT_IsUnbreakableTD
import Definitions.Def_SingleExpBisect_Main_NodeData

set_option autoImplicit false

open scoped Classical

open SingleExpBisect.Main

open MinBisectFPT

private lemma mem_cutEdges_mk {n : ℕ} (H : SimpleGraph (Fin n)) (X : Finset (Fin n)) (a b : Fin n) :
    s(a, b) ∈ cutEdges H X ↔ H.Adj a b ∧ ((a ∈ X ∧ b ∉ X) ∨ (b ∈ X ∧ a ∉ X)) := by
  simp only [cutEdges, Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.mem_edgeSet,
    Sym2.eq_iff]
  constructor
  · rintro ⟨hadj, u, hu, v, hv, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · exact ⟨hadj, Or.inl ⟨hu, hv⟩⟩
    · exact ⟨hadj, Or.inr ⟨hu, hv⟩⟩
  · rintro ⟨hadj, (⟨ha, hb⟩ | ⟨hb, ha⟩)⟩
    · exact ⟨hadj, a, ha, b, hb, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨hadj, b, hb, a, ha, Or.inr ⟨rfl, rfl⟩⟩

private lemma mu_le {n : ℕ} (G : SimpleGraph (Fin n)) (W S A : Finset (Fin n)) (h : A ∩ W = S) :
    mu G W S ≤ cutSize G A :=
  Nat.sInf_le ⟨A, h, rfl⟩

private lemma mu_attained {n : ℕ} (G : SimpleGraph (Fin n)) (W S : Finset (Fin n)) (hS : S ⊆ W) :
    ∃ A : Finset (Fin n), A ∩ W = S ∧ cutSize G A = mu G W S :=
  Nat.sInf_mem (s := {c : ℕ | ∃ A : Finset (Fin n), A ∩ W = S ∧ cutSize G A = c})
    ⟨cutSize G S, S, Finset.inter_eq_left.mpr hS, rfl⟩

private lemma cut_compl {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n)) :
    cutSize G Xᶜ = cutSize G X := by
  unfold cutSize
  congr 1
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    simp only [mem_cutEdges_mk, Finset.mem_compl]
    tauto

private lemma mu_compl {n : ℕ} (G : SimpleGraph (Fin n)) (W A : Finset (Fin n)) (ha : A ⊆ W) :
    mu G W (W \ A) = mu G W A := by
  have h (A : Finset (Fin n)) (ha : A ⊆ W) : mu G W (W \ A) ≤ mu G W A := by
    obtain ⟨X, hx, hcut⟩ := mu_attained G W A ha
    have he : Xᶜ ∩ W = W \ A := by rw [← hx]; ext v; simp; tauto
    simpa only [cut_compl, hcut] using mu_le G W (W \ A) Xᶜ he
  have he : W \ (W \ A) = A := Finset.sdiff_sdiff_eq_self ha
  exact le_antisymm (h A ha) (by simpa only [he] using h (W \ A) Finset.sdiff_subset)

private lemma p2m_map_sum {ι M N : Type*} (f : M → N) (s : Finset ι)
    (x : ι → AddMonoidAlgebra ℚ M) :
    AddMonoidAlgebra.mapDomain f (∑ a ∈ s, x a) =
    ∑ a ∈ s, AddMonoidAlgebra.mapDomain f (x a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp only [Finset.sum_insert hi, AddMonoidAlgebra.mapDomain_add, ih]

private noncomputable def tm {n : ℕ} (A : Finset (Fin n)) (j : ℕ) : LPoly n :=
  toL (MvPolynomial.monomial (Finsupp.single Var.w j + yMono A) (1 : ℚ))

private lemma p2m_flip {n : ℕ} (W A : Finset (Fin n)) (ha : A ⊆ W) (c : ℕ) :
    yProdL W * invY (tm A c) = tm (W \ A) c := by
  classical
  simp only [tm, toL, yProdL, invY, ← MvPolynomial.single_eq_monomial,
    AddMonoidAlgebra.mapDomain_single, AddMonoidAlgebra.single_mul_single, mul_one]
  congr 1
  ext v
  have ind (U : Finset (Fin n)) (x : Fin n) :
      yMono U (Var.y x) = if x ∈ U then 1 else 0 := by
    simp [yMono, Finsupp.finsetSum_apply, Finsupp.single_apply, eq_comm]
  simp only [Finsupp.add_apply, Finsupp.sub_apply, Finsupp.filter_apply, Finsupp.mapRange_apply]
  cases v with
  | y x =>
    have hh : IsYVar (Var.y x) := ⟨x,rfl⟩
    by_cases hx : x ∈ A <;> by_cases hw : x ∈ W <;>
      simp [hh, hx, hw, Finsupp.finsetSum_apply, Finsupp.single_apply, ind] <;> exact hw (ha hx)
  | x =>
    simp [IsYVar, yMono, Finsupp.finsetSum_apply]
  | x' =>
    simp [IsYVar, yMono, Finsupp.finsetSum_apply]
  | w =>
    simp [IsYVar, yMono, Finsupp.finsetSum_apply]

theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) (W B : Finset (Fin n)) (hBW : B ⊆ W) (k : ℕ)
    (hB : 4 * k + 1 < B.card) (hunb : IsEdgeUnbreakable G Finset.univ B (2 * k) k) :
    toL (Zfull G W k) = toL (Zle G W B k) + yProdL W * invY (toL (Zle G W B k)) := by
  classical
  let P := W.powerset.filter fun A => mu G W A ≤ k
  let small := fun A : Finset (Fin n) => (A ∩ B).card ≤ 2 * k
  let F := fun A : Finset (Fin n) => tm A (mu G W A)
  let Q := P.filter small
  let R := P.filter (fun A => ¬small A)
  have hp {A} : A ∈ P ↔ A ⊆ W ∧ mu G W A ≤ k := by simp [P]
  have hQ : W.powerset.filter (fun A => mu G W A ≤ k ∧ (A ∩ B).card ≤ 2*k) = Q := by
    ext a; simp [Q, P, small, and_assoc]
  have hf : toL (Zfull G W k) = ∑ A ∈ P, F A := by
    simp only [toL, Zfull, tm, P, F, p2m_map_sum]
  have hq : toL (Zle G W B k) = ∑ A ∈ Q, F A := by
    simp only [Zle, hQ, toL, p2m_map_sum, F, tm]
  have hinv (A : Finset (Fin n)) (ha : A ⊆ W) : W \ (W \ A) = A := by
    exact Finset.sdiff_sdiff_eq_self ha
  have hc {A} (hA : A ∈ P) : W \ A ∈ P :=
    hp.mpr ⟨Finset.sdiff_subset, (mu_compl G W A (hp.mp hA).1).le.trans (hp.mp hA).2⟩
  have hclass {A} (hA : A ∈ P) : small (W \ A) ↔ ¬ small A := by
    obtain ⟨X, hx, hx'⟩ := mu_attained G W A (hp.mp hA).1
    have e1 : X ∩ B = A ∩ B := by rw [←hx]; ext x; simp only [Finset.mem_inter]; constructor <;> aesop
    have e2 : (W \ A) ∩ B = B \ X := by rw [←hx]; ext x; simp only [Finset.mem_sdiff, Finset.mem_inter]; constructor <;> aesop
    have hh := hunb X (Finset.subset_univ X) (hx' ▸ (hp.mp hA).2)
    have he := Finset.card_sdiff_add_card_inter B X
    rw [Finset.inter_comm B X] at he
    change ((W \ A) ∩ B).card ≤ 2*k ↔ ¬ (A ∩ B).card ≤ 2*k
    rw [e2, ←e1]
    omega
  rw [hf, hq]
  have hpart : (∑ A ∈ Q, F A) + (∑ A ∈ R, F A) = ∑ A ∈ P, F A := by
    exact Finset.sum_filter_add_sum_filter_not P small F
  rw [←hpart, add_right_inj, invY, p2m_map_sum, Finset.mul_sum]
  refine Finset.sum_bij' (fun A _ => W \ A) (fun A _ => W \ A) ?_ ?_ ?_ ?_ ?_
  · intro A hA
    obtain ⟨hpA, ha⟩ := Finset.mem_filter.mp hA
    exact Finset.mem_filter.mpr ⟨hc hpA, (hclass hpA).mpr ha⟩
  · intro A hA
    obtain ⟨hpA, ha⟩ := Finset.mem_filter.mp hA
    exact Finset.mem_filter.mpr ⟨hc hpA, fun h => (hclass hpA).mp h ha⟩
  · intro A hA
    exact hinv A (hp.mp (Finset.mem_filter.mp hA).1).1
  · intro A hA
    exact hinv A (hp.mp (Finset.mem_filter.mp hA).1).1
  · intro A hA
    have ha := (hp.mp (Finset.mem_filter.mp hA).1).1
    change tm A _ = yProdL W * invY (tm (W \ A) (mu G W (W \ A)))
    rw [p2m_flip _ _ Finset.sdiff_subset, hinv A ha, mu_compl G W A ha]
