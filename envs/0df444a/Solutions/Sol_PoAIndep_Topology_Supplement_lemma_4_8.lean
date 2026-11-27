-- Prove2me | solution 1 for PoAIndep.Topology.Supplement.lemma_4_8
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:33:20.942233+00:00
-- url     : https://prove2.me/submissions/1d849913-7cb2-41cb-8914-d4cd302e8395

import Mathlib
import Definitions.Def_PoAIndep_Topology_Model
import Definitions.Def_PoAIndep_Topology_Supplement_Inhomogeneous
import Definitions.Def_PoAIndep_Topology_Supplement_UnionOfPaths

open PoAIndep
open PoAIndep.Topology
open PoAIndep.Topology.Supplement

open PoAIndep.Topology

theorem solution (L : Set (ℝ → ℝ)) (hL : IsStandardClass L) (hi : IsInhomogeneous L) :
    ∀ b : ENNReal, b < anarchyValue L →
      ∃ (nV nE : ℕ) (I : Instance (Fin nV) (Fin nE)),
        IsUnionOfPathsInstance I ∧ InClass I L ∧
          ∃ f g : Flow I,
            IsFlow I f ∧ IsFeasible I f ∧ IsNashFlow I f ∧
            IsFlow I g ∧ IsFeasible I g ∧ 0 < cost I g ∧
            b < ENNReal.ofReal (cost I f / cost I g) := by
              intro b hb
              obtain ⟨ℓ, hℓL, hb1⟩ : ∃ ℓ ∈ L, b < anarchyValueFn ℓ := by
                simpa [anarchyValue, lt_iSup_iff] using hb
              obtain ⟨h, hhL, hh0⟩ := hi
              have hℓlat : IsLatency ℓ := (hL.2 ℓ hℓL).1
              have hhlat : IsLatency h := (hL.2 h hhL).1
              have key : ∀ (N' M' K' : ℕ) (r lam x : ℝ), 0 < r → 0 ≤ lam → lam ≤ 1 → 0 ≤ x →
                  lam * r + (K' + 1) * x = r → ((N':ℝ) + 1) * ℓ r ≤ ((M':ℝ) + 1) * h 0 →
                  ∃ (nV nE : ℕ) (I : Instance (Fin nV) (Fin nE)),
                    IsUnionOfPathsInstance I ∧ InClass I L ∧
                      ∃ f g : Flow I,
                        IsFlow I f ∧ IsFeasible I f ∧ IsNashFlow I f ∧
                        IsFlow I g ∧ IsFeasible I g ∧ cost I f = ((N':ℝ) + 1) * ℓ r * r ∧
                        cost I g = ((N':ℝ) + 1) * ℓ (lam * r) * (lam * r) + ((K':ℝ) + 1) * (((M':ℝ) + 1) * h x * x) := by
                intro N' M' K' r lam x hr hlam0 hlam1 hx hsum hNash
                obtain ⟨tgt0, htA, htB⟩ : ∃ tgt0 : Fin (N'+1) ⊕ (Fin (K'+1) × Fin (M'+1)) → Fin 2 ⊕ (Fin N' ⊕ (Fin (K'+1) × Fin M')),
                    (∀ p : Fin (N'+1), tgt0 (Sum.inl p) = if hp : (p:ℕ) < N' then Sum.inr (Sum.inl ⟨p, hp⟩) else Sum.inl 1) ∧
                    (∀ j (p : Fin (M'+1)), tgt0 (Sum.inr (j,p)) = if hp : (p:ℕ) < M' then Sum.inr (Sum.inr (j, ⟨p, hp⟩)) else Sum.inl 1) :=
                  ⟨fun e => Sum.elim (fun p : Fin (N'+1) => if hp : (p:ℕ) < N' then Sum.inr (Sum.inl ⟨p, hp⟩) else Sum.inl 1)
                    (fun q : Fin (K'+1) × Fin (M'+1) => if hp : (q.2:ℕ) < M' then Sum.inr (Sum.inr (q.1, ⟨q.2, hp⟩)) else Sum.inl 1) e,
                    fun p => rfl, fun j p => rfl⟩
                obtain ⟨src0, hsA, hsB⟩ : ∃ src0 : Fin (N'+1) ⊕ (Fin (K'+1) × Fin (M'+1)) → Fin 2 ⊕ (Fin N' ⊕ (Fin (K'+1) × Fin M')),
                    (∀ p : Fin (N'+1), src0 (Sum.inl p) = if hp : (p:ℕ) = 0 then Sum.inl 0 else Sum.inr (Sum.inl ⟨p - 1, by omega⟩)) ∧
                    (∀ j (p : Fin (M'+1)), src0 (Sum.inr (j,p)) = if hp : (p:ℕ) = 0 then Sum.inl 0 else Sum.inr (Sum.inr (j, ⟨p - 1, by omega⟩))) :=
                  ⟨fun e => Sum.elim (fun p : Fin (N'+1) => if hp : (p:ℕ) = 0 then Sum.inl 0 else Sum.inr (Sum.inl ⟨p - 1, by omega⟩))
                    (fun q : Fin (K'+1) × Fin (M'+1) => if hp : (q.2:ℕ) = 0 then Sum.inl 0 else Sum.inr (Sum.inr (q.1, ⟨q.2 - 1, by omega⟩))) e,
                    fun p => rfl, fun j p => rfl⟩
                set A0 : List (Fin (N'+1) ⊕ (Fin (K'+1) × Fin (M'+1))) := List.ofFn (fun p => Sum.inl p) with hA0
                set B0 : Fin (K'+1) → List (Fin (N'+1) ⊕ (Fin (K'+1) × Fin (M'+1))) :=
                  fun j => List.ofFn (fun p => Sum.inr (j, p)) with hB0
                have simpA : IsSimplePath src0 tgt0 A0 (Sum.inl 0) (Sum.inl 1) := by
                  refine ⟨by simp [hA0], ?_, ?_, ?_, ?_⟩
                  · rw [hA0, List.isChain_ofFn]
                    intro i hi
                    simp [htA, hsA, show i < N' by omega]
                  · simp [hA0, List.ofFn_succ, hsA]
                  · rw [hA0, List.ofFn_succ', List.concat_eq_append, List.getLast?_append]
                    simp [htA]
                  · rw [List.nodup_cons]
                    refine ⟨?_, ?_⟩
                    · simp only [hA0, List.map_ofFn, List.mem_ofFn, Function.comp_apply, htA, not_exists]
                      intro p
                      split_ifs <;> simp
                    · rw [hA0, List.map_ofFn, List.nodup_ofFn]
                      intro p q hpq
                      simp only [Function.comp_apply, htA] at hpq
                      apply Fin.ext
                      split_ifs at hpq with h1 h2 h2 <;> simp at hpq <;> omega
                have simpB : ∀ j, IsSimplePath src0 tgt0 (B0 j) (Sum.inl 0) (Sum.inl 1) := by
                  intro j
                  refine ⟨by simp [hB0], ?_, ?_, ?_, ?_⟩
                  · rw [hB0, List.isChain_ofFn]
                    intro i hi
                    simp [htB, hsB, show i < M' by omega]
                  · simp [hB0, List.ofFn_succ, hsB]
                  · rw [hB0]
                    simp only
                    rw [List.ofFn_succ', List.concat_eq_append, List.getLast?_append]
                    simp [htB]
                  · rw [List.nodup_cons]
                    refine ⟨?_, ?_⟩
                    · simp only [hB0, List.map_ofFn, List.mem_ofFn, Function.comp_apply, htB, not_exists]
                      intro p
                      split_ifs <;> simp
                    · rw [hB0]
                      simp only
                      rw [List.map_ofFn, List.nodup_ofFn]
                      intro p q hpq
                      simp only [Function.comp_apply, htB] at hpq
                      apply Fin.ext
                      split_ifs at hpq with h1 h2 h2 <;> simp at hpq <;> omega
                have memA : ∀ e, e ∈ A0 ↔ ∃ p, e = Sum.inl p := by
                  intro e; simp only [hA0, List.mem_ofFn]
                  constructor <;> rintro ⟨p, hp⟩ <;> exact ⟨p, hp.symm⟩
                have memB : ∀ j e, e ∈ B0 j ↔ ∃ p, e = Sum.inr (j, p) := by
                  intro j e; simp only [hB0, List.mem_ofFn]
                  constructor <;> rintro ⟨p, hp⟩ <;> exact ⟨p, hp.symm⟩
                have tgtA : ∀ w ∈ A0.map tgt0, w = Sum.inl 1 ∨ ∃ p, w = Sum.inr (Sum.inl p) := by
                  intro w hw
                  simp only [hA0, List.map_ofFn, List.mem_ofFn, Function.comp_apply, htA] at hw
                  obtain ⟨p, hp⟩ := hw
                  split_ifs at hp with h1
                  · exact Or.inr ⟨_, hp.symm⟩
                  · exact Or.inl hp.symm
                have tgtB : ∀ j, ∀ w ∈ (B0 j).map tgt0, w = Sum.inl 1 ∨ ∃ p, w = Sum.inr (Sum.inr (j, p)) := by
                  intro j w hw
                  simp only [hB0, List.map_ofFn, List.mem_ofFn, Function.comp_apply, htB] at hw
                  obtain ⟨p, hp⟩ := hw
                  split_ifs at hp with h1
                  · exact Or.inr ⟨_, hp.symm⟩
                  · exact Or.inl hp.symm
                have cover0 : ∀ w, w = Sum.inl 0 ∨ w ∈ A0.map tgt0 ∨ ∃ j, w ∈ (B0 j).map tgt0 := by
                  intro w
                  rcases w with w | w | w
                  · fin_cases w
                    · exact Or.inl rfl
                    · right; left
                      simp only [hA0, List.map_ofFn, List.mem_ofFn, Function.comp_apply, htA]
                      exact ⟨Fin.last N', by simp⟩
                  · right; left
                    simp only [hA0, List.map_ofFn, List.mem_ofFn, Function.comp_apply, htA]
                    exact ⟨⟨w, by omega⟩, by simp⟩
                  · right; right
                    refine ⟨w.1, ?_⟩
                    simp only [hB0, List.map_ofFn, List.mem_ofFn, Function.comp_apply, htB]
                    exact ⟨⟨w.2, by omega⟩, by simp⟩
                set P0 : Fin (K' + 1 + 1) → List (Fin (N'+1) ⊕ (Fin (K'+1) × Fin (M'+1))) :=
                  fun j => Fin.cases A0 B0 j with hP0
                have disj0 : ∀ j j', j ≠ j' → ∀ w, w ∈ (P0 j).map tgt0 → w ∈ (P0 j').map tgt0 → w = Sum.inl 1 := by
                  intro j j' hjj w hw hw'
                  induction j using Fin.cases with
                  | zero =>
                    induction j' using Fin.cases with
                    | zero => exact absurd rfl hjj
                    | succ j' =>
                      simp only [hP0, Fin.cases_zero, Fin.cases_succ] at hw hw'
                      rcases tgtA w hw with h1 | ⟨p, rfl⟩
                      · exact h1
                      · rcases tgtB j' _ hw' with h2 | ⟨q, h2⟩ <;> simp at h2
                  | succ j =>
                    induction j' using Fin.cases with
                    | zero =>
                      simp only [hP0, Fin.cases_zero, Fin.cases_succ] at hw hw'
                      rcases tgtA w hw' with h1 | ⟨p, rfl⟩
                      · exact h1
                      · rcases tgtB j _ hw with h2 | ⟨q, h2⟩ <;> simp at h2
                    | succ j' =>
                      simp only [hP0, Fin.cases_zero, Fin.cases_succ] at hw hw'
                      have hne : j ≠ j' := fun h => hjj (by rw [h])
                      rcases tgtB j w hw with h1 | ⟨p, rfl⟩
                      · exact h1
                      · rcases tgtB j' _ hw' with h2 | ⟨q, h2⟩
                        · simp at h2
                        · simp at h2; exact absurd h2.1 hne
                set eE := Fintype.equivFin (Fin (N'+1) ⊕ (Fin (K'+1) × Fin (M'+1))) with heE
                set eV := Fintype.equivFin (Fin 2 ⊕ (Fin N' ⊕ (Fin (K'+1) × Fin M'))) with heV
                set lat0 : Fin (N'+1) ⊕ (Fin (K'+1) × Fin (M'+1)) → ℝ → ℝ := fun e => Sum.elim (fun _ => ℓ) (fun _ => h) e with hlat0
                have htr : ∀ (P : List (Fin (N'+1) ⊕ (Fin (K'+1) × Fin (M'+1)))) u v, IsSimplePath src0 tgt0 P u v →
                    IsSimplePath (fun e => eV (src0 (eE.symm e))) (fun e => eV (tgt0 (eE.symm e))) (P.map eE) (eV u) (eV v) := by
                  rintro P u v ⟨h1, h2, h3, h4, h5⟩
                  refine ⟨by simpa using h1, ?_, ?_, ?_, ?_⟩
                  · rw [List.isChain_map]; simpa using h2
                  · rw [List.head?_map, Option.map_map]
                    rw [show ((fun e => eV (src0 (eE.symm e))) ∘ eE) = eV ∘ src0 by ext; simp, ← Option.map_map, h3]; rfl
                  · rw [List.getLast?_map, Option.map_map]
                    rw [show ((fun e => eV (tgt0 (eE.symm e))) ∘ eE) = eV ∘ tgt0 by ext; simp, ← Option.map_map, h4]; rfl
                  · have : (eV u :: List.map (fun e => eV (tgt0 (eE.symm e))) (List.map eE P)) = (u :: P.map tgt0).map eV := by
                      simp [Function.comp_def]
                    rw [this]; exact h5.map eV.injective
                let I : Instance (Fin (Fintype.card (Fin 2 ⊕ (Fin N' ⊕ (Fin (K'+1) × Fin M')))))
                    (Fin (Fintype.card (Fin (N'+1) ⊕ (Fin (K'+1) × Fin (M'+1))))) :=
                  { src := fun e => eV (src0 (eE.symm e))
                    tgt := fun e => eV (tgt0 (eE.symm e))
                    k := 1
                    s := fun _ => eV (Sum.inl 0)
                    t := fun _ => eV (Sum.inl 1)
                    r := fun _ => r
                    ℓ := fun e => lat0 (eE.symm e)
                    r_pos := fun _ => hr
                    paths_nonempty := fun _ => ⟨A0.map eE, htr _ _ _ simpA⟩
                    latency := by
                      intro e
                      rcases eE.symm e with p | q
                      · exact hℓlat
                      · exact hhlat }
                have simpP : ∀ j, IsSimplePath I.src I.tgt ((P0 j).map eE) (I.s 0) (I.t 0) := by
                  intro j
                  induction j using Fin.cases with
                  | zero => exact htr _ _ _ simpA
                  | succ j => exact htr _ _ _ (simpB j)
                have hmapt : ∀ L0 : List (Fin (N'+1) ⊕ (Fin (K'+1) × Fin (M'+1))), (L0.map eE).map I.tgt = (L0.map tgt0).map eV := by
                  intro L0; simp [I, Function.comp_def]
                refine ⟨_, _, I, ⟨rfl, fun i => ⟨K' + 2, fun j => (P0 j).map eE, by omega, fun j => simpP j, ?_, ?_, ?_⟩⟩, ?_, ?_⟩
                · intro e
                  obtain ⟨e0, rfl⟩ : ∃ e0, e = eE e0 := ⟨eE.symm e, by simp⟩
                  rcases e0 with p | q
                  · refine ⟨0, ?_, ?_⟩
                    · simp [hP0, memA]
                    · intro j hj
                      induction j using Fin.cases with
                      | zero => rfl
                      | succ j =>
                        simp only [hP0, Fin.cases_succ, List.mem_map, EmbeddingLike.apply_eq_iff_eq, exists_eq_right] at hj
                        obtain ⟨p', hp'⟩ := (memB j _).1 hj
                        simp at hp'
                  · refine ⟨q.1.succ, ?_, ?_⟩
                    · simp only [hP0, Fin.cases_succ, List.mem_map, EmbeddingLike.apply_eq_iff_eq, exists_eq_right]
                      exact (memB _ _).2 ⟨q.2, rfl⟩
                    · intro j hj
                      induction j using Fin.cases with
                      | zero =>
                        simp only [hP0, Fin.cases_zero, List.mem_map, EmbeddingLike.apply_eq_iff_eq, exists_eq_right] at hj
                        obtain ⟨p', hp'⟩ := (memA _).1 hj
                        simp at hp'
                      | succ j =>
                        simp only [hP0, Fin.cases_succ, List.mem_map, EmbeddingLike.apply_eq_iff_eq, exists_eq_right] at hj
                        obtain ⟨p', hp'⟩ := (memB j _).1 hj
                        rw [Sum.inr.injEq, Prod.ext_iff] at hp'
                        rw [hp'.1]
                · intro j j' hjj v hv hv'
                  rw [hmapt, List.mem_map] at hv hv'
                  obtain ⟨w, hw, rfl⟩ := hv
                  obtain ⟨w', hw', hww⟩ := hv'
                  have := eV.injective hww
                  rw [this] at hw'
                  rw [disj0 j j' hjj w hw hw']
                · intro v
                  obtain ⟨w, rfl⟩ : ∃ w, v = eV w := ⟨eV.symm v, by simp⟩
                  rcases cover0 w with h1 | h1 | ⟨j, h1⟩
                  · left; rw [h1]
                  · right; refine ⟨0, ?_⟩
                    rw [hmapt]; exact List.mem_map_of_mem h1
                  · right; refine ⟨j.succ, ?_⟩
                    rw [hmapt]; exact List.mem_map_of_mem h1
                · intro e
                  show lat0 (eE.symm e) ∈ L
                  rcases eE.symm e with p | q
                  · exact hℓL
                  · exact hhL
                set A := A0.map eE with hA
                set B := fun j => (B0 j).map eE with hB
                have hmemA : ∀ e0, eE e0 ∈ A ↔ e0 ∈ A0 := by intro e0; simp [hA]
                have hmemB : ∀ j e0, eE e0 ∈ B j ↔ e0 ∈ B0 j := by intro j e0; simp [hB]
                have hAB : ∀ j, A ≠ B j := by
                  intro j hj
                  have : eE (Sum.inl 0) ∈ B j := hj ▸ (hmemA _).2 ((memA _).2 ⟨0, rfl⟩)
                  obtain ⟨p, hp⟩ := (memB j _).1 ((hmemB j _).1 this)
                  simp at hp
                have hBB : ∀ j j', B j = B j' → j = j' := by
                  intro j j' hj
                  have : eE (Sum.inr (j, 0)) ∈ B j' := hj ▸ (hmemB _ _).2 ((memB _ _).2 ⟨0, rfl⟩)
                  obtain ⟨p, hp⟩ := (memB j' _).1 ((hmemB j' _).1 this)
                  simp at hp; exact hp.1
                have hEF : ∀ (F : List (Fin (Fintype.card (Fin (N'+1) ⊕ (Fin (K'+1) × Fin (M'+1))))) →₀ ℝ) e,
                    edgeFlow I (fun _ => F) e = F.sum (fun P x => if e ∈ P then x else 0) := by
                  intro F e; simp [edgeFlow, I]
                have hC : ∀ (F : List (Fin (Fintype.card (Fin (N'+1) ⊕ (Fin (K'+1) × Fin (M'+1))))) →₀ ℝ),
                    cost I (fun _ => F) = F.sum (fun P x => pathLatency I (fun _ => F) P * x) := by
                  intro F; simp [cost, I]
                have hz : ∀ (e : Fin (Fintype.card (Fin (N'+1) ⊕ (Fin (K'+1) × Fin (M'+1))))) (P : List _), (if e ∈ P then (0:ℝ) else 0) = 0 := by
                  intros; simp
                have hadd : ∀ (e : Fin (Fintype.card (Fin (N'+1) ⊕ (Fin (K'+1) × Fin (M'+1))))) (P : List _) (a b : ℝ),
                    (if e ∈ P then a + b else 0) = (if e ∈ P then a else 0) + (if e ∈ P then b else 0) := by
                  intros; split_ifs <;> simp
                have hlatA : ∀ p, I.ℓ (eE (Sum.inl p)) = ℓ := by intro p; simp [I, hlat0]
                have hlatB : ∀ j p, I.ℓ (eE (Sum.inr (j, p))) = h := by intro j p; simp [I, hlat0]
                -- path latency of A when all A-edges carry the same flow
                have hPLA : ∀ (F : Flow I) (y : ℝ), (∀ p, edgeFlow I F (eE (Sum.inl p)) = y) →
                    pathLatency I F A = ((N':ℝ) + 1) * ℓ y := by
                  intro F y hy
                  simp only [pathLatency, hA, hA0, List.map_map, List.map_ofFn]
                  simp [Function.comp_def, hlatA, hy, List.sum_ofFn]; ring
                have hPLB : ∀ (F : Flow I) (y : ℝ) j, (∀ p, edgeFlow I F (eE (Sum.inr (j, p))) = y) →
                    pathLatency I F (B j) = ((M':ℝ) + 1) * h y := by
                  intro F y j hy
                  simp only [pathLatency, hB, hB0, List.map_map, List.map_ofFn]
                  simp [Function.comp_def, hlatB, hy, List.sum_ofFn]; ring
                have tele : ∀ (φ : Fin (Fintype.card (Fin 2 ⊕ (Fin N' ⊕ (Fin (K'+1) × Fin M')))) → ℝ) (P : List _) u v,
                    P ≠ [] → List.IsChain (fun e e' => I.tgt e = I.src e') P → P.head?.map I.src = some u →
                    P.getLast?.map I.tgt = some v → (P.map fun e => φ (I.tgt e) - φ (I.src e)).sum = φ v - φ u := by
                  intro φ P
                  induction P with
                  | nil => intro u v hP; exact absurd rfl hP
                  | cons a l ih =>
                    intro u v _ h2 h3 h4
                    cases l with
                    | nil =>
                      simp at h3 h4; simp [h3, h4]
                    | cons b l' =>
                      rw [List.isChain_cons_cons] at h2
                      have := ih (I.src b) v (by simp) h2.2 (by simp) (by simpa using h4)
                      simp only [List.map_cons, List.sum_cons] at this ⊢
                      simp at h3
                      rw [this, h2.1, ← h3]; ring
                obtain ⟨φ0, hφs, hφt, hφA, hφB⟩ : ∃ φ0 : Fin 2 ⊕ (Fin N' ⊕ (Fin (K'+1) × Fin M')) → ℝ,
                    φ0 (Sum.inl 0) = 0 ∧ φ0 (Sum.inl 1) = ((N':ℝ) + 1) * ℓ r ∧
                    (∀ p : Fin N', φ0 (Sum.inr (Sum.inl p)) = ((p:ℕ) + 1) * ℓ r) ∧
                    (∀ j (p : Fin M'), φ0 (Sum.inr (Sum.inr (j, p))) = ((p:ℕ) + 1) * ((((N':ℝ) + 1) * ℓ r) / ((M':ℝ) + 1))) :=
                  ⟨Sum.elim (fun i : Fin 2 => if i = 0 then 0 else ((N':ℝ) + 1) * ℓ r)
                    (Sum.elim (fun p : Fin N' => (((p:ℕ):ℝ) + 1) * ℓ r)
                      (fun q : Fin (K'+1) × Fin M' => (((q.2:ℕ):ℝ) + 1) * ((((N':ℝ) + 1) * ℓ r) / ((M':ℝ) + 1)))),
                    by simp, by simp, fun p => rfl, fun j p => rfl⟩
                have incA : ∀ p, φ0 (tgt0 (Sum.inl p)) - φ0 (src0 (Sum.inl p)) = ℓ r := by
                  intro p
                  rw [htA, hsA]
                  split_ifs with h1 h2 h2
                  · rw [hφA, hφs]; simp [h2]
                  · rw [hφA, hφA]; rw [Nat.cast_sub (by omega : 1 ≤ (p:ℕ))]; push_cast; ring
                  · rw [hφt, hφs]
                    have : (N':ℝ) = 0 := by exact_mod_cast (show N' = 0 by omega)
                    rw [this]; ring
                  · rw [hφt, hφA]
                    have : (N':ℝ) = (p:ℕ) := by exact_mod_cast (show N' = p by omega)
                    rw [this, Nat.cast_sub (by omega : 1 ≤ (p:ℕ))]; push_cast; ring
                have incB : ∀ j p, φ0 (tgt0 (Sum.inr (j, p))) - φ0 (src0 (Sum.inr (j, p))) = (((N':ℝ) + 1) * ℓ r) / ((M':ℝ) + 1) := by
                  intro j p
                  have hM : ((M':ℝ) + 1) ≠ 0 := by positivity
                  rw [htB, hsB]
                  split_ifs with h1 h2 h2
                  · rw [hφB, hφs]; simp [h2]
                  · rw [hφB, hφB]; rw [Nat.cast_sub (by omega : 1 ≤ (p:ℕ))]; push_cast; ring
                  · rw [hφt, hφs]
                    have : (M':ℝ) = 0 := by exact_mod_cast (show M' = 0 by omega)
                    rw [this]; ring
                  · rw [hφt, hφB]
                    have : (M':ℝ) = (p:ℕ) := by exact_mod_cast (show M' = p by omega)
                    rw [this, Nat.cast_sub (by omega : 1 ≤ (p:ℕ))]; push_cast; field_simp; ring
                have hEF1 : ∀ P y e, edgeFlow I (fun _ => Finsupp.single P y) e = if e ∈ P then y else 0 := by
                  intro P y e; rw [hEF, Finsupp.sum_single_index (by simp)]
                have hEFs : ∀ (F : List (Fin (Fintype.card (Fin (N'+1) ⊕ (Fin (K'+1) × Fin (M'+1))))) →₀ ℝ) P₁ P₂ δ e,
                    edgeFlow I (fun _ => F - Finsupp.single P₁ δ + Finsupp.single P₂ δ) e =
                      edgeFlow I (fun _ => F) e - (if e ∈ P₁ then δ else 0) + (if e ∈ P₂ then δ else 0) := by
                  intro F P₁ P₂ δ e
                  rw [hEF, hEF, Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by split_ifs <;> simp), Finsupp.sum_sub_index,
                    Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
                  intro P a b; split_ifs <;> simp
                have hupd : ∀ (F G : List (Fin (Fintype.card (Fin (N'+1) ⊕ (Fin (K'+1) × Fin (M'+1))))) →₀ ℝ) (i : Fin I.k),
                    Function.update (fun _ : Fin I.k => F) i G = fun _ => G := by
                  intro F G i
                  funext i'
                  have : i' = i := Fin.ext (by have h1 := i.2; have h2 := i'.2; simp only [I] at h1 h2; omega)
                  subst this; simp
                have hφ : ∀ e, φ0 (eV.symm (I.tgt e)) = φ0 (tgt0 (eE.symm e)) ∧ φ0 (eV.symm (I.src e)) = φ0 (src0 (eE.symm e)) := by
                  intro e; simp [I]
                have hflowA : ∀ p, edgeFlow I (fun _ => Finsupp.single A r) (eE (Sum.inl p)) = r := by
                  intro p; rw [hEF1, if_pos ((hmemA _).2 ((memA _).2 ⟨p, rfl⟩))]
                have costf : cost I (fun _ => Finsupp.single A r) = ((N':ℝ) + 1) * ℓ r * r := by
                  rw [hC, Finsupp.sum_single_index (by simp), hPLA _ r hflowA]
                have nashf : IsNashFlow I (fun _ => Finsupp.single A r) := by
                  intro i P₁ P₂ hP₁ hP₂ hpos δ hδ
                  have h1 : P₁ = A := by
                    by_contra hne
                    simp [Finsupp.single_apply, Ne.symm hne] at hpos
                  subst h1
                  rw [hPLA _ r hflowA]
                  simp only at hδ ⊢
                  rw [hupd]
                  obtain ⟨hn, hch, hhd, hlast, -⟩ := hP₂
                  have ht := tele (fun v => φ0 (eV.symm v)) P₂ _ _ hn hch hhd hlast
                  simp only [I, Equiv.symm_apply_apply, hφs, hφt] at ht
                  rw [pathLatency]
                  calc ((N':ℝ)+1) * ℓ r = (P₂.map fun e => φ0 (tgt0 (eE.symm e)) - φ0 (src0 (eE.symm e))).sum := by
                        rw [ht]; ring
                    _ ≤ _ := by
                      apply List.sum_le_sum
                      intro e he
                      rw [hEFs, hEF1, if_pos he]
                      obtain ⟨e0, rfl⟩ : ∃ e0, e = eE e0 := ⟨eE.symm e, by simp⟩
                      rw [Equiv.symm_apply_apply]
                      rcases e0 with p | ⟨j, p⟩
                      · have hA' := (hmemA _).2 ((memA _).2 ⟨p, rfl⟩)
                        rw [incA, hlatA, if_pos hA', if_pos hA', sub_add_cancel]
                      · have hnot : eE (Sum.inr (j,p)) ∉ A := fun hh => by
                          obtain ⟨q, hq⟩ := (memA _).1 ((hmemA _).1 hh); simp at hq
                        rw [incB, hlatB, if_neg hnot, if_neg hnot, sub_zero, zero_add]
                        calc _ ≤ h 0 := (div_le_iff₀ (by positivity)).2 (by linarith [hNash])
                          _ ≤ h δ := hhlat.2.2 (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hδ.1.le) hδ.1.le
                set G : List (Fin (Fintype.card (Fin (N'+1) ⊕ (Fin (K'+1) × Fin (M'+1))))) →₀ ℝ :=
                  Finsupp.single A (lam * r) + ∑ j, Finsupp.single (B j) x with hG
                have hEFG : ∀ e, edgeFlow I (fun _ => G) e = (if e ∈ A then lam * r else 0) + ∑ j, (if e ∈ B j then x else 0) := by
                  intro e
                  rw [hEF, hG, Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by split_ifs <;> simp),
                    ← Finsupp.sum_finsetSum_index (fun _ => by simp) (fun _ _ _ => by split_ifs <;> simp),
                    Finsupp.sum_single_index (by simp)]
                  congr 1
                  apply Finset.sum_congr rfl
                  intro j _
                  rw [Finsupp.sum_single_index (by simp)]
                have hGA : ∀ p, edgeFlow I (fun _ => G) (eE (Sum.inl p)) = lam * r := by
                  intro p
                  rw [hEFG, if_pos ((hmemA _).2 ((memA _).2 ⟨p, rfl⟩))]
                  rw [Finset.sum_eq_zero, add_zero]
                  intro j _
                  rw [if_neg]
                  intro hh
                  obtain ⟨q, hq⟩ := (memB j _).1 ((hmemB j _).1 hh); simp at hq
                have hGB : ∀ j p, edgeFlow I (fun _ => G) (eE (Sum.inr (j, p))) = x := by
                  intro j p
                  rw [hEFG, if_neg (fun hh => by obtain ⟨q, hq⟩ := (memA _).1 ((hmemA _).1 hh); simp at hq), zero_add]
                  rw [Finset.sum_eq_single j]
                  · rw [if_pos ((hmemB _ _).2 ((memB _ _).2 ⟨p, rfl⟩))]
                  · intro j' _ hj'
                    rw [if_neg]
                    intro hh
                    obtain ⟨q, hq⟩ := (memB j' _).1 ((hmemB j' _).1 hh)
                    simp at hq; exact hj' hq.1.symm
                  · simp
                have costg : cost I (fun _ => G) = ((N':ℝ) + 1) * ℓ (lam * r) * (lam * r) + ((K':ℝ) + 1) * (((M':ℝ) + 1) * h x * x) := by
                  rw [hC]
                  conv_lhs => rw [hG]
                  rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring),
                    ← Finsupp.sum_finsetSum_index (fun _ => by simp) (fun _ _ _ => by ring),
                    Finsupp.sum_single_index (by simp), hPLA _ _ hGA]
                  rw [Finset.sum_congr rfl (fun j _ => by rw [Finsupp.sum_single_index (by simp), hPLB _ _ j (hGB j)])]
                  simp
                refine ⟨fun _ => Finsupp.single A r, fun _ => G, ?_, ?_, nashf, ?_, ?_, costf, costg⟩
                · intro i
                  refine ⟨fun P => ?_, fun P hP => ?_⟩
                  · simp only [Finsupp.single_apply]; split_ifs <;> linarith
                  · rw [Finsupp.support_single_ne_zero _ hr.ne', Finset.mem_singleton] at hP
                    subst hP; exact simpP 0
                · intro i
                  show (Finsupp.single A r).sum (fun _ y => y) = r
                  rw [Finsupp.sum_single_index rfl]
                · intro i
                  refine ⟨fun P => ?_, fun P hP => ?_⟩
                  · show 0 ≤ G P
                    rw [hG, Finsupp.add_apply, Finsupp.finset_sum_apply]
                    apply add_nonneg
                    · simp only [Finsupp.single_apply]; split_ifs
                      · exact mul_nonneg hlam0 hr.le
                      · exact le_rfl
                    · apply Finset.sum_nonneg; intro j _
                      simp only [Finsupp.single_apply]; split_ifs
                      · exact hx
                      · exact le_rfl
                  · rw [Finsupp.mem_support_iff] at hP
                    by_cases hPA : P = A
                    · subst hPA; exact simpP 0
                    by_cases hPB : ∃ j, P = B j
                    · obtain ⟨j, rfl⟩ := hPB; exact simpP j.succ
                    exfalso; apply hP
                    show G P = 0
                    push_neg at hPB
                    rw [hG, Finsupp.add_apply, Finsupp.finset_sum_apply]
                    simp [Finsupp.single_apply, Ne.symm hPA, fun j => Ne.symm (hPB j)]
                · intro i
                  show G.sum (fun _ y => y) = r
                  rw [hG, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
                    ← Finsupp.sum_finsetSum_index (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
                  simp [Finsupp.sum_single_index]
                  linarith
              simp only [anarchyValueFn, lt_iSup_iff] at hb1
              obtain ⟨r, hr, hℓr, lam, hlam, -, hb2⟩ := hb1
              set D := lam * (ℓ (lam * r) / ℓ r) + (1 - lam) with hD
              have hlr0 : 0 ≤ ℓ (lam * r) := hℓlat.1 _ (mul_nonneg hlam.1 hr.le)
              have hDpos : 0 < D := by
                rcases eq_or_lt_of_le hlam.2 with h1 | h1
                · rw [hD, h1]; simp [hℓr.ne']
                · have : 0 ≤ lam * (ℓ (lam*r)/ℓ r) := mul_nonneg hlam.1 (div_nonneg hlr0 hℓr.le)
                  linarith
              have hbtop : b ≠ ⊤ := ne_top_of_lt hb2
              have hbb : b = ENNReal.ofReal b.toReal := (ENNReal.ofReal_toReal hbtop).symm
              have hb'0 : 0 ≤ b.toReal := ENNReal.toReal_nonneg
              have hb'D : b.toReal < D⁻¹ := by
                rw [hbb] at hb2; exact (ENNReal.ofReal_lt_ofReal_iff (inv_pos.2 hDpos)).1 hb2
              have hbD : b.toReal * D < 1 := by
                have := mul_lt_mul_of_pos_right hb'D hDpos
                rwa [inv_mul_cancel₀ hDpos.ne'] at this
              have hc : 0 < h 0 := lt_of_le_of_ne (hhlat.1 0 le_rfl) (Ne.symm hh0)
              obtain ⟨N', hN'⟩ : ∃ N' : ℕ, 2 * b.toReal * h 0 < ((N':ℝ)+1) * ℓ r * (1 - b.toReal * D) := by
                obtain ⟨n, hn⟩ := exists_nat_gt (2 * b.toReal * h 0 / (ℓ r * (1 - b.toReal * D)))
                refine ⟨n, ?_⟩
                have hpos : 0 < ℓ r * (1 - b.toReal * D) := mul_pos hℓr (by linarith)
                rw [div_lt_iff₀ hpos] at hn
                nlinarith
              have hTpos : 0 < ((N':ℝ)+1) * ℓ r := by positivity
              obtain ⟨M', hM'⟩ : ∃ M' : ℕ, ⌈((N':ℝ)+1) * ℓ r / h 0⌉₊ = M' + 1 :=
                ⟨⌈((N':ℝ)+1) * ℓ r / h 0⌉₊ - 1, by have := Nat.ceil_pos.2 (div_pos hTpos hc); omega⟩
              have hMc1 : ((N':ℝ)+1) * ℓ r ≤ ((M':ℝ)+1) * h 0 := by
                have := Nat.le_ceil (((N':ℝ)+1) * ℓ r / h 0)
                rw [hM'] at this; push_cast at this
                rwa [div_le_iff₀ hc] at this
              have hMc2 : ((M':ℝ)+1) * h 0 < ((N':ℝ)+1) * ℓ r + h 0 := by
                have := Nat.ceil_lt_add_one (div_pos hTpos hc).le
                rw [hM'] at this; push_cast at this
                have h2 : ((M':ℝ)+1) - 1 < ((N':ℝ)+1) * ℓ r / h 0 := by linarith
                rw [lt_div_iff₀ hc] at h2; linarith
              have hcont : ContinuousWithinAt h (Set.Ici 0) 0 :=
                hhlat.2.1.continuousOn.continuousWithinAt (Set.mem_Ici.2 le_rfl)
              obtain ⟨δ, hδ, hδh⟩ := Metric.continuousWithinAt_iff.1 hcont (h 0 / ((M':ℝ)+1)) (by positivity)
              obtain ⟨K', hK'⟩ : ∃ K' : ℕ, (1 - lam) * r / δ < (K':ℝ) + 1 := by
                obtain ⟨n, hn⟩ := exists_nat_gt ((1 - lam) * r / δ); exact ⟨n, by linarith⟩
              have h1l : 0 ≤ 1 - lam := by linarith [hlam.2]
              set x := (1 - lam) * r / ((K':ℝ)+1) with hxdef
              have hx0 : 0 ≤ x := div_nonneg (mul_nonneg h1l hr.le) (by positivity)
              have hxδ : x < δ := by
                rw [hxdef, div_lt_iff₀ (by positivity)]; rw [div_lt_iff₀ hδ] at hK'; linarith
              have hhx : h x < h 0 + h 0 / ((M':ℝ)+1) := by
                have := hδh (Set.mem_Ici.2 hx0) (by rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hx0]; exact hxδ)
                rw [Real.dist_eq] at this; linarith [(abs_lt.1 this).2]
              have hhx0 : h 0 ≤ h x := hhlat.2.2 (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx0) hx0
              have hsum : lam * r + ((K':ℝ)+1) * x = r := by
                rw [hxdef]; field_simp; ring
              obtain ⟨nV, nE, I, hU, hCl, f, g, hf1, hf2, hf3, hg1, hg2, hcf, hcg⟩ :=
                key N' M' K' r lam x hr hlam.1 hlam.2 hx0 hsum hMc1
              have hKx : ((K':ℝ)+1) * x = (1 - lam) * r := by rw [hxdef]; field_simp
              have hcg2 : cost I g = ((N':ℝ) + 1) * ℓ (lam * r) * (lam * r) + ((M':ℝ) + 1) * h x * ((1 - lam) * r) := by
                rw [hcg, ← hKx]; ring
              have hgpos : 0 < cost I g := by
                rw [hcg2]
                rcases eq_or_lt_of_le hlam.2 with h1 | h1
                · rw [h1]; simp; positivity
                · have : 0 < ((M':ℝ) + 1) * h x * ((1 - lam) * r) :=
                    mul_pos (mul_pos (by positivity) (by linarith)) (mul_pos (by linarith) hr)
                  have : 0 ≤ ((N':ℝ) + 1) * ℓ (lam * r) * (lam * r) := by
                    have := mul_nonneg hlam.1 hr.le; positivity
                  linarith
              have e1 : ((M':ℝ)+1) * h x ≤ ((N':ℝ)+1) * ℓ r + 2 * h 0 := by
                have h3 : ((M':ℝ)+1) * (h 0 + h 0 / ((M':ℝ)+1)) = ((M':ℝ)+1) * h 0 + h 0 := by field_simp
                have := mul_lt_mul_of_pos_left hhx (by positivity : (0:ℝ) < (M':ℝ)+1)
                linarith
              have e2 : lam * ℓ (lam * r) = D * ℓ r - (1 - lam) * ℓ r := by
                rw [hD]; field_simp; ring
              have hcgle : cost I g ≤ ((N':ℝ)+1) * ℓ r * D * r + 2 * h 0 * r := by
                rw [hcg2]
                have h4 := mul_le_mul_of_nonneg_right e1 (mul_nonneg h1l hr.le)
                have h5 : ((N':ℝ) + 1) * ℓ (lam * r) * (lam * r) = ((N':ℝ) + 1) * r * (lam * ℓ (lam * r)) := by ring
                rw [h5, e2]
                have h6 : 0 ≤ 2 * h 0 * r * lam :=
                  mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 2 * h 0) hr.le) hlam.1
                have h9 : ((N':ℝ) + 1) * r * (D * ℓ r - (1 - lam) * ℓ r) + ((M':ℝ) + 1) * h x * ((1 - lam) * r) =
                    ((N':ℝ)+1) * ℓ r * D * r + 2 * h 0 * r - 2 * h 0 * r * lam -
                      ((((N':ℝ)+1) * ℓ r + 2 * h 0) * ((1 - lam) * r) - ((M':ℝ) + 1) * h x * ((1 - lam) * r)) := by ring
                rw [h9]; linarith [h4, h6]
              refine ⟨nV, nE, I, hU, hCl, f, g, hf1, hf2, hf3, hg1, hg2, hgpos, ?_⟩
              rw [hbb]
              apply (ENNReal.ofReal_lt_ofReal_iff (div_pos (by rw [hcf]; positivity) hgpos)).2
              rw [lt_div_iff₀ hgpos, hcf]
              have h7 := mul_le_mul_of_nonneg_left hcgle hb'0
              have h8 : b.toReal * (((N':ℝ)+1) * ℓ r * D * r + 2 * h 0 * r) < ((N':ℝ) + 1) * ℓ r * r := by
                have := mul_lt_mul_of_pos_right hN' hr
                have h10 : b.toReal * (((N':ℝ)+1) * ℓ r * D * r + 2 * h 0 * r) = ((N':ℝ) + 1) * ℓ r * r -
                    (((N':ℝ)+1) * ℓ r * (1 - b.toReal * D) * r - 2 * b.toReal * h 0 * r) := by ring
                rw [h10]; linarith
              linarith
