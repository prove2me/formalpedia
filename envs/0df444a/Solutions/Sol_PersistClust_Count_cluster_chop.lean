-- Prove2me | solution 1 for PersistClust.Count.cluster_chop
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-14T06:47:03.539972+00:00
-- url     : https://prove2.me/submissions/48f41e56-6585-4d63-b39b-95cf6e0ea794

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

private theorem exists_clusterChop : ∀ (k : ℕ) (B : Finset ℝ), B.card ≤ k → B.Nonempty →
    ∀ (ε : ℝ), 0 ≤ ε →
    ∃ c ∈ B, (∀ w ∈ B, c ≤ w) ∧ ∃ d ∈ B,
      (∀ t : ℝ, c - ε ≤ t → t ≤ d + ε → ∃ w ∈ B, c ≤ w ∧ w ≤ d ∧ |w - t| ≤ ε) ∧
      (∀ v ∈ B, d < v → d + 2 * ε < v) ∧ c ≤ d := by
  intro k
  induction k with
  | zero =>
    intro B hcard hB ε hε
    have h0 : B = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [h0] at hB
    exact absurd hB (by simp)
  | succ k ih =>
    intro B hcard hB ε hε
    have hmB : B.max' hB ∈ B := Finset.max'_mem _ hB
    have hle : ∀ v ∈ B, v ≤ B.max' hB := fun v hv =>
      (Finset.isGreatest_max' B hB).2 (Finset.mem_coe.mpr hv)
    have hcard' : (B.erase (B.max' hB)).card ≤ k := by
      have h1 := Finset.card_erase_add_one hmB
      omega
    rcases (B.erase (B.max' hB)).eq_empty_or_nonempty with hB'e | hB'ne
    · -- B.erase max = ∅: B is a singleton; chop at its unique element
      have hsingle : ∀ v ∈ B, v = B.max' hB := by
        intro v hv
        by_contra hne
        have hvm : v ∈ B.erase (B.max' hB) := Finset.mem_erase.mpr ⟨hne, hv⟩
        rw [hB'e] at hvm
        exact absurd hvm (by simp)
      refine ⟨B.max' hB, hmB, fun w hw => le_of_eq (hsingle w hw).symm, B.max' hB, hmB,
        ?_, ?_, le_refl _⟩
      · intro t ht1 ht2
        exact ⟨B.max' hB, hmB, le_refl _, le_refl _, abs_le.mpr ⟨by linarith, by linarith⟩⟩
      · intro v hv hvlt
        rw [hsingle v hv] at hvlt
        exact absurd hvlt (lt_irrefl _)
    · -- B' := B.erase max is nonempty: take its chop and lift the minimum to B
      obtain ⟨c', hc'B', hc'min, d', hd'B', hnet', hfar', hc'd'⟩ :=
        ih (B.erase (B.max' hB)) hcard' hB'ne ε hε
      have hc'B : c' ∈ B := Finset.mem_of_mem_erase hc'B'
      have hd'B : d' ∈ B := Finset.mem_of_mem_erase hd'B'
      have hcmB : ∀ w ∈ B, c' ≤ w := by
        intro w hw
        by_cases hw' : w = B.max' hB
        · rw [hw']; exact hle c' hc'B
        · exact hc'min w (Finset.mem_erase.mpr ⟨hw', hw⟩)
      by_cases hA : ∀ v ∈ B.erase (B.max' hB), v ≤ d'
      · by_cases hsw : B.max' hB ≤ d' + 2 * ε
        · -- swallow: the max extends the net by one ≤ 2ε step; chop at the max
          refine ⟨c', hc'B, hcmB, B.max' hB, hmB, ?_, ?_, hle c' hc'B⟩
          · intro t ht1 ht2
            by_cases ht : t ≤ d' + ε
            · obtain ⟨w, hwB', hcw, hwd, hwabs⟩ := hnet' t ht1 ht
              exact ⟨w, Finset.mem_of_mem_erase hwB', hcw, hwd.trans (hle d' hd'B), hwabs⟩
            · have ht' : d' + ε < t := not_le.mp ht
              exact ⟨B.max' hB, hmB, hle c' hc'B, le_refl _,
                abs_le.mpr ⟨by linarith, by linarith⟩⟩
          · intro v hv hvlt
            exact absurd (hle v hv) (not_le.mpr hvlt)
        · -- the max is itself the first far jump: the chop stays at d'
          have hmaxlt : d' + 2 * ε < B.max' hB := not_le.mp hsw
          refine ⟨c', hc'B, hcmB, d', hd'B, ?_, ?_, hc'd'⟩
          · intro t ht1 ht2
            obtain ⟨w, hwB', hcw, hwd, hwabs⟩ := hnet' t ht1 ht2
            exact ⟨w, Finset.mem_of_mem_erase hwB', hcw, hwd, hwabs⟩
          · intro v hv hvlt
            by_cases hvm : v = B.max' hB
            · rw [hvm]; exact hmaxlt
            · exact absurd (hA v (Finset.mem_erase.mpr ⟨hvm, hv⟩)) (not_le.mpr hvlt)
      · -- B' already cut below its own top: d' still chops B (the max sits above the far rest)
        obtain ⟨v₀, hv₀, hv₀lt⟩ : ∃ v ∈ B.erase (B.max' hB), d' < v := by
          by_contra hcon
          have hcon' : ∀ v ∈ B.erase (B.max' hB), v ≤ d' := fun v hv =>
            le_of_not_gt fun hvlt => hcon ⟨v, hv, hvlt⟩
          exact hA hcon'
        refine ⟨c', hc'B, hcmB, d', hd'B, ?_, ?_, hc'd'⟩
        · intro t ht1 ht2
          obtain ⟨w, hwB', hcw, hwd, hwabs⟩ := hnet' t ht1 ht2
          exact ⟨w, Finset.mem_of_mem_erase hwB', hcw, hwd, hwabs⟩
        · intro v hv hvlt
          by_cases hvm : v = B.max' hB
          · rw [hvm]
            exact (hfar' v₀ hv₀ hv₀lt).trans_le (hle v₀ (Finset.mem_of_mem_erase hv₀))
          · exact hfar' v (Finset.mem_erase.mpr ⟨hvm, hv⟩) hvlt

/-- T5 lane tool (CHOP-6 lane, 2026-10-14): internal-cluster-chop generalization of
`t5_cluster_assembly`. `hnet` here takes the NET-WITNESS form: it only asserts the slice
cover `supply L R ⊆ ⋃ (slice fibers)` when the births of the `s`-slice over `[L, R]` form
an ε-net of the expanded window `[L − ε, R + ε]`. For sparse `s` the full-span net
property is FALSE (2-point counterexample: births `10 * ε` apart, mid-window junk), so the
sibling's one-shot full-window assembly is unavailable; instead the birth Finset is
CHOPPED at the first `> 2 * ε` adjacent gap, the count splits additively over the
chop-induced split `s = C ⊔ s'` (fiber-union disjointness from `hdisj`), the `C`-bound
comes from `hwin` plus the per-cluster net (witness search along the sorted births), and
`s'` (fewer births) goes through the induction on distinct-birth cardinality. -/
theorem solution {X Q : Type}
    (ε : ℝ) (hε : 0 ≤ ε) (bth : X → ℝ) (s : Set X) (hs : s.Finite)
    (fib : X → Set Q) (supply : ℝ → ℝ → Set Q)
    (hwin : ∀ L R : ℝ, L ≤ R → {x : X | L ≤ bth x ∧ bth x ≤ R}.encard ≤ (supply L R).encard)
    (hcone : ∀ (L R : ℝ), L ≤ R → ∀ x ∈ s, L ≤ bth x → bth x ≤ R → fib x ⊆ supply L R)
    (hnet : ∀ L R : ℝ, L ≤ R →
        (∀ t : ℝ, L - ε ≤ t → t ≤ R + ε →
          ∃ x ∈ s, L ≤ bth x ∧ bth x ≤ R ∧ |bth x - t| ≤ ε) →
        supply L R ⊆ ⋃ x ∈ {x ∈ s | L ≤ bth x ∧ bth x ≤ R}, fib x)
    (hdisj : ∀ x ∈ s, ∀ x' ∈ s, ∀ t : ℝ, bth x ≤ t → t + 2 * ε < bth x' → fib x ∩ fib x' = ∅) :
    s.encard ≤ (⋃ x ∈ s, fib x).encard := by
  rcases s.eq_empty_or_nonempty with h | ⟨x₀, hx₀⟩
  · subst h
    exact (le_of_eq Set.encard_empty).trans zero_le
  · obtain ⟨m, hm, hmin⟩ := s.exists_min_image bth hs ⟨x₀, hx₀⟩
    have main : ∀ (n : ℕ) (T : Set X) (u : ℝ), T.encard ≤ n → T = {x ∈ s | u < bth x} →
        T.encard ≤ (⋃ x ∈ T, fib x).encard := by
      intro n
      induction n with
      | zero =>
        intro T u hTn hTeq
        rcases T.eq_empty_or_nonempty with hT | ⟨x, hx⟩
        · subst hT
          exact (le_of_eq Set.encard_empty).trans zero_le
        · rw [Nat.cast_zero] at hTn
          exact absurd hTn (not_le.mpr (Set.encard_pos.mpr ⟨x, hx⟩))
      | succ k ih =>
        intro T u hTn hTeq
        rcases T.eq_empty_or_nonempty with hT | ⟨x₀, hx₀⟩
        · subst hT
          exact (le_of_eq Set.encard_empty).trans zero_le
        · have hTsub : T ⊆ s := by
            intro x hx
            rw [hTeq] at hx
            exact hx.1
          have hTfin : T.Finite := hs.subset hTsub
          have hBne : (hTfin.toFinset.image bth).Nonempty :=
            ⟨bth x₀, Finset.mem_image_of_mem bth ((Set.Finite.mem_toFinset hTfin).mpr hx₀)⟩
          obtain ⟨c, hcB, hcmin, d, hdB, hchnet, hfar, hcd⟩ :=
            exists_clusterChop (hTfin.toFinset.image bth).card
              (hTfin.toFinset.image bth) (le_refl _) hBne ε hε
          have hBmem : ∀ x ∈ T, bth x ∈ hTfin.toFinset.image bth :=
            fun _ hx => Finset.mem_image_of_mem bth ((Set.Finite.mem_toFinset hTfin).mpr hx)
          have hmem : ∀ w ∈ hTfin.toFinset.image bth, ∃ x ∈ T, bth x = w := by
            intro w hw
            obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hw
            exact ⟨x, (Set.Finite.mem_toFinset hTfin).mp hx, rfl⟩
          obtain ⟨x_c, hx_c, hc_eq⟩ := hmem c hcB
          obtain ⟨x_d, hx_d, hd_eq⟩ := hmem d hdB
          have hu_c : u < c := by
            have hx' := hx_c
            rw [hTeq] at hx'
            have h2 := hx'.2
            rwa [hc_eq] at h2
          have hsplitC : T = {x ∈ T | bth x ≤ d} ∪ {x ∈ T | d < bth x} := by
            ext x
            constructor
            · intro hx
              rcases lt_or_ge d (bth x) with h1 | h1
              · exact Or.inr ⟨hx, h1⟩
              · exact Or.inl ⟨hx, h1⟩
            · intro hx
              rcases hx with hx | hx
              · exact hx.1
              · exact hx.1
          have hdisjCT : Disjoint {x ∈ T | bth x ≤ d} {x ∈ T | d < bth x} := by
            rw [Set.disjoint_iff]
            intro x hx1
            exact absurd hx1.2.2 (by have := hx1.1.2; linarith)
          have hcard_split : T.encard = {x ∈ T | bth x ≤ d}.encard +
              {x ∈ T | d < bth x}.encard :=
            (congrArg Set.encard hsplitC).trans (Set.encard_union_eq hdisjCT)
          have hCne : {x ∈ T | bth x ≤ d}.Nonempty := ⟨x_d, hx_d, le_of_eq hd_eq⟩
          have hsliceeq : {x ∈ s | c ≤ bth x ∧ bth x ≤ d} = {x ∈ T | bth x ≤ d} := by
            ext x
            constructor
            · intro hx
              have hut : u < bth x := by
                have := hu_c
                have := hx.2.1
                linarith
              refine ⟨?_, hx.2.2⟩
              rw [hTeq]
              exact ⟨hx.1, hut⟩
            · intro hx
              exact ⟨hTsub hx.1, hcmin (bth x) (hBmem x hx.1), hx.2⟩
          have hnetCD : supply c d ⊆ ⋃ x ∈ {x ∈ T | bth x ≤ d}, fib x := by
            have hprem : ∀ t : ℝ, c - ε ≤ t → t ≤ d + ε →
                ∃ x ∈ s, c ≤ bth x ∧ bth x ≤ d ∧ |bth x - t| ≤ ε := by
              intro t ht1 ht2
              obtain ⟨w, hwB, hcw, hwd, hwabs⟩ := hchnet t ht1 ht2
              obtain ⟨x, hx, rfl⟩ := hmem w hwB
              exact ⟨x, hTsub hx, hcw, hwd, hwabs⟩
            have hnet1 := hnet c d hcd hprem
            rwa [hsliceeq] at hnet1
          have hCbound : {x ∈ T | bth x ≤ d}.encard ≤
              (⋃ x ∈ {x ∈ T | bth x ≤ d}, fib x).encard := by
            calc {x ∈ T | bth x ≤ d}.encard ≤ {x : X | c ≤ bth x ∧ bth x ≤ d}.encard :=
                  Set.encard_le_encard (fun x hx => ⟨hcmin (bth x) (hBmem x hx.1), hx.2⟩)
              _ ≤ (supply c d).encard := hwin c d hcd
              _ ≤ (⋃ x ∈ {x ∈ T | bth x ≤ d}, fib x).encard := Set.encard_le_encard hnetCD
          have hfiDisj : Disjoint (⋃ x ∈ {x ∈ T | bth x ≤ d}, fib x)
              (⋃ x ∈ {x ∈ T | d < bth x}, fib x) := by
            rw [Set.disjoint_iff]
            intro q hq1
            obtain ⟨hq1, hq2⟩ := hq1
            obtain ⟨x, hx, hqf⟩ := Set.mem_iUnion₂.mp hq1
            obtain ⟨x', hx', hqf'⟩ := Set.mem_iUnion₂.mp hq2
            have hcross : fib x ∩ fib x' = ∅ :=
              hdisj x (hTsub hx.1) x' (hTsub hx'.1) d hx.2
                (hfar (bth x') (hBmem x' hx'.1) hx'.2)
            have hqmem : q ∈ fib x ∩ fib x' := ⟨hqf, hqf'⟩
            rw [hcross] at hqmem
            exact absurd hqmem (by simp)
          have hT'eq : {x ∈ T | d < bth x} = {x ∈ s | d + 2 * ε < bth x} := by
            ext x
            constructor
            · intro hx
              exact ⟨hTsub hx.1, hfar (bth x) (hBmem x hx.1) hx.2⟩
            · intro hx
              have hut : u < bth x := by
                have := hu_c
                have := hcd
                have := hx.2
                linarith
              refine ⟨?_, ?_⟩
              · rw [hTeq]
                exact ⟨hx.1, hut⟩
              · have := hx.2
                linarith
          have hCfin : {x ∈ T | bth x ≤ d}.Finite := hTfin.subset fun x hx => hx.1
          have hT'fin : {x ∈ T | d < bth x}.Finite := hTfin.subset fun x hx => hx.1
          have hT'card : {x ∈ T | d < bth x}.encard ≤ (k : ℕ∞) := by
            have e2 : {x ∈ T | bth x ≤ d}.encard = (hCfin.toFinset.card : ℕ∞) :=
              hCfin.encard_eq_coe_toFinset_card
            have e3 : {x ∈ T | d < bth x}.encard = (hT'fin.toFinset.card : ℕ∞) :=
              hT'fin.encard_eq_coe_toFinset_card
            have hTn2 := hTn
            rw [hcard_split, e2, e3, ← ENat.natCast_add] at hTn2
            have hN := ENat.natCast_le_natCast.mp hTn2
            have hCpos : 1 ≤ hCfin.toFinset.card :=
              Finset.one_le_card.mpr (hCfin.toFinset_nonempty.mpr hCne)
            rw [e3, ENat.natCast_le_natCast]
            omega
          have hIH := ih {x ∈ T | d < bth x} (d + 2 * ε) hT'card hT'eq
          have hlast : (⋃ x ∈ {x ∈ T | bth x ≤ d}, fib x) ∪
              (⋃ x ∈ {x ∈ T | d < bth x}, fib x) = ⋃ x ∈ T, fib x := by
            rw [← Set.biUnion_union, ← hsplitC]
          calc T.encard = {x ∈ T | bth x ≤ d}.encard + {x ∈ T | d < bth x}.encard :=
                hcard_split
            _ ≤ (⋃ x ∈ {x ∈ T | bth x ≤ d}, fib x).encard +
                (⋃ x ∈ {x ∈ T | d < bth x}, fib x).encard :=
                add_le_add hCbound hIH
            _ = ((⋃ x ∈ {x ∈ T | bth x ≤ d}, fib x) ∪
                (⋃ x ∈ {x ∈ T | d < bth x}, fib x)).encard :=
                (Set.encard_union_eq hfiDisj).symm
            _ = (⋃ x ∈ T, fib x).encard := by rw [hlast]
    have hcard : s.encard ≤ (hs.toFinset.card : ℕ∞) :=
      le_of_eq hs.encard_eq_coe_toFinset_card
    have hs' : s = {x ∈ s | bth m - 1 < bth x} := by
      ext x
      constructor
      · intro hx
        exact ⟨hx, by have := hmin x hx; linarith⟩
      · exact fun hx => hx.1
    exact main _ s (bth m - 1) hcard hs'
