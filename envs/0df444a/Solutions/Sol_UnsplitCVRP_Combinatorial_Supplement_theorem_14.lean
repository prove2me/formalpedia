-- Prove2me | solution 1 for UnsplitCVRP.Combinatorial.Supplement.theorem_14
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:19:20.224801+00:00
-- url     : https://prove2.me/submissions/38f5bc61-eb43-47ed-8a19-53d95540674a

import Mathlib
import Definitions.Def_SupplyChainTheory_vrp
import Definitions.Def_UnsplitCVRP_Combinatorial_Setting
import Definitions.Def_UnsplitCVRP_Combinatorial_Supplement_ConfigLP

open UnsplitCVRP
open UnsplitCVRP.Combinatorial
open UnsplitCVRP.Combinatorial.Supplement

/-- Theorem 14, p. 11 (inner `min` repaired to `max`): taking the better of Algorithm 2's
output and the solution `B δ'` of Theorem 13 [BTV21] costs, in expectation, at most
`max {3 + f δ', ln 2 + α + (1-δ')/(1-δ)}` times every feasible solution's cost, for every
`δ' ∈ (0, 1)`. -/
theorem solution {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hc : SupplyChainTheory.VRPMetric c) (d : Fin (n + 1) → ℝ)
    (hd : Demands d) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (α : ℝ)
    (xstar : List (Fin (n + 1)) → ℝ) (hx : IsConfigOptimal c d δ xstar)
    (tour : Finset (Fin (n + 1)) → List (Fin (n + 1)))
    (htour : ∀ U ⊆ clients n, IsTourOn U (tour U))
    (hctour : ∀ U ⊆ clients n, SupplyChainTheory.routeCost c (tour U) ≤ α * tspOn c U)
    (f : ℝ → ℝ) (B : ℝ → List (List (Fin (n + 1))))
    (hB : ∀ δ', 0 < δ' → δ' < 1 → IsSolution d (B δ'))
    (hBcost : ∀ δ', 0 < δ' → δ' < 1 → ∀ R, IsSolution d R →
      (1 - δ') * SupplyChainTheory.solutionCost c R ≤ radial c d (clients n) →
      SupplyChainTheory.solutionCost c (B δ') ≤ (3 + f δ') * SupplyChainTheory.solutionCost c R) :
    ∀ δ', 0 < δ' → δ' < 1 →
      (∀ S ∈ (configTours d δ).powerset, ∃ R, IsSolution d R ∧
        SupplyChainTheory.solutionCost c R ≤
          min (alg2Cost c d tour S) (SupplyChainTheory.solutionCost c (B δ'))) ∧
      ∀ R, IsSolution d R →
        expect d δ (Real.log 2) xstar
            (fun S => min (alg2Cost c d tour S) (SupplyChainTheory.solutionCost c (B δ'))) ≤
          max (3 + f δ') (Real.log 2 + α + (1 - δ') / (1 - δ)) *
            SupplyChainTheory.solutionCost c R := by
              have P1 : ∀ (A : List (Fin (n + 1))), (∀ v ∈ A, 0 < d v ∧ d v ≤ 1) → ∀ θ : ℝ, 0 ≤ θ → θ < 1 - δ →
                  bestSplit c d A ≤ SupplyChainTheory.routeCost c A + addedCost c d δ A θ := by
                intro A hA θ hθ0 hθ1
                classical
                have hrc : ∀ L : List (Fin (n + 1)), SupplyChainTheory.routeCost c L =
                    (List.zipWith c (0 :: L) (L ++ [0])).sum := by
                  intro L
                  simp [SupplyChainTheory.routeCost, SupplyChainTheory.closedLength]
                have htri : ∀ (a x : Fin (n + 1)) (M : List (Fin (n + 1))),
                    (List.zipWith c (a :: M) (M ++ [0])).sum ≤
                      c a x + (List.zipWith c (x :: M) (M ++ [0])).sum := by
                  intro a x M
                  cases M with
                  | nil => simpa using hc.triangle a 0 x
                  | cons y M =>
                    simp only [List.cons_append, List.zipWith_cons_cons, List.sum_cons]
                    have := hc.triangle a y x
                    linarith
                have hZnn : ∀ (a : Fin (n + 1)) (M : List (Fin (n + 1))),
                    0 ≤ (List.zipWith c (a :: M) (M ++ [0])).sum := by
                  intro a M
                  apply List.sum_nonneg
                  intro y hy
                  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hy
                  rw [List.getElem_zipWith]
                  exact hc.nonneg _ _
                set L := 1 - δ with hL
                have hL0 : 0 < L := by linarith
                set m := A.length with hm
                set P : ℕ → ℝ := fun i => prefixLoad d A i with hPdef
                have hP0 : P 0 = 0 := by simp [hPdef, prefixLoad, load]
                have hPs : ∀ k, k < m → P (k + 1) = P k + d (A.getD k 0) := by
                  intro k hk
                  simp only [hPdef, prefixLoad, load]
                  rw [List.getD_eq_getElem _ _ hk, List.take_add_one, List.map_append, List.sum_append,
                    List.getElem?_eq_getElem hk]
                  simp
                have hG : ∀ ρ : ℝ, 0 ≤ ρ → ∃ ℓ : ℕ, ρ < θ + ℓ * L ∧ θ + ℓ * L ≤ ρ + L := by
                  intro ρ hρ
                  by_cases hρθ : ρ < θ
                  · exact ⟨0, by simpa using hρθ, by simp; linarith⟩
                  · push_neg at hρθ
                    set t := (ρ - θ) / L with ht
                    have ht0 : 0 ≤ t := div_nonneg (by linarith) hL0.le
                    refine ⟨⌊t⌋₊ + 1, ?_, ?_⟩
                    · have := Nat.lt_floor_add_one t
                      have e : ρ = θ + t * L := by rw [ht]; field_simp; ring
                      push_cast
                      rw [e]; nlinarith
                    · have := Nat.floor_le ht0
                      have e : ρ = θ + t * L := by rw [ht]; field_simp; ring
                      push_cast
                      rw [e]; nlinarith
                set term : ℕ → ℝ := fun i =>
                  (if IsBad d δ A i θ then 2 * c 0 (A.getD i 0) else 0) +
                   (if δ < d (A.getD i 0) ∧ IsFourCopies d δ A i θ then 2 * c 0 (A.getD i 0) else 0)
                  with htermdef
                have hterm0 : ∀ i, 0 ≤ term i := by
                  intro i
                  have := hc.nonneg 0 (A.getD i 0)
                  simp only [htermdef]
                  split_ifs <;> linarith
                have hclose : ∀ (H' : List (Fin (n + 1))) (R' : List (List (Fin (n + 1)))),
                    (∀ L ∈ R', L ≠ [] ∧ load d L ≤ 1) → load d H' ≤ 1 →
                    ∃ R'' : List (List (Fin (n + 1))), R''.flatten = H' ++ R'.flatten ∧
                      (∀ L ∈ R'', L ≠ [] ∧ load d L ≤ 1) ∧
                      (R''.map (SupplyChainTheory.routeCost c)).sum =
                        (List.zipWith c (0 :: H') (H' ++ [0])).sum + (R'.map (SupplyChainTheory.routeCost c)).sum := by
                  intro H' R' hR' hH'
                  by_cases hH : H' = []
                  · subst hH
                    refine ⟨R', by simp, hR', ?_⟩
                    simp [hc.refl]
                  · refine ⟨H' :: R', by simp, ?_, ?_⟩
                    · intro L hL
                      rcases List.mem_cons.1 hL with rfl | hL
                      · exact ⟨hH, hH'⟩
                      · exact hR' L hL
                    · simp [hrc]
                have key : ∀ j k, k + j = m → ∀ (x : Fin (n + 1)) (lam : ℝ), 0 ≤ lam → 0 ≤ P k - lam →
                    (∀ ℓ : ℕ, ¬ (P k - lam < θ + ℓ * L ∧ θ + ℓ * L ≤ P k)) →
                    ∃ (H : List (Fin (n + 1))) (R : List (List (Fin (n + 1)))),
                      H ++ R.flatten = A.drop k ∧ (∀ L ∈ R, L ≠ [] ∧ load d L ≤ 1) ∧ lam + load d H ≤ 1 ∧
                      (List.zipWith c (x :: H) (H ++ [0])).sum + (R.map (SupplyChainTheory.routeCost c)).sum ≤
                        (List.zipWith c (x :: A.drop k) (A.drop k ++ [0])).sum + ∑ i ∈ Finset.Ico k m, term i := by
                  intro j
                  induction j with
                  | zero =>
                    intro k hk x lam hlam hρ hno
                    obtain ⟨ℓ, h1, h2⟩ := hG _ hρ
                    have h3 : P k < θ + ℓ * L := by
                      by_contra hcon; push_neg at hcon; exact hno ℓ ⟨h1, hcon⟩
                    refine ⟨[], [], ?_, by simp, ?_, ?_⟩
                    · simp only [List.flatten_nil, List.append_nil]
                      rw [List.drop_eq_nil_of_le (by omega)]
                    · simp [load]; linarith
                    · rw [List.drop_eq_nil_of_le (by omega), show k = m by omega]
                      simp
                  | succ j ih =>
                    intro k hk x lam hlam hρ hno
                    have hkm : k < m := by omega
                    set a := A.getD k 0 with ha
                    have haA : a ∈ A := by rw [ha, List.getD_eq_getElem _ _ hkm]; exact List.getElem_mem hkm
                    obtain ⟨hda0, hda1⟩ := hA a haA
                    have hdrop : A.drop k = a :: A.drop (k + 1) := by
                      rw [ha, List.getD_eq_getElem _ _ hkm]; exact List.drop_eq_getElem_cons hkm
                    have hsum : ∑ i ∈ Finset.Ico k m, term i = term k + ∑ i ∈ Finset.Ico (k + 1) m, term i :=
                      Finset.sum_eq_sum_Ico_succ_bot hkm _
                    have hPk := hPs k hkm
                    rw [← ha] at hPk
                    rw [hdrop, hsum]
                    set M := A.drop (k + 1) with hM
                    have hca := hc.symm a 0
                    by_cases hbad : IsBad d δ A k θ
                    · obtain ⟨ℓ₂, h21, h22⟩ := hbad
                      change P k < _ at h21
                      change _ ≤ P (k + 1) at h22
                      obtain ⟨ℓ₁, h11, h12⟩ := hG _ hρ
                      have h13 : P k < θ + ℓ₁ * L := by
                        by_contra hcon; push_neg at hcon; exact hno ℓ₁ ⟨h11, hcon⟩
                      have hE : ∃ ℓ : ℕ, P k < θ + ℓ * L ∧ θ + ℓ * L ≤ P k + d a ∧
                          θ + ℓ * L ≤ P k - lam + L := by
                        by_cases h : θ + ℓ₂ * L ≤ θ + ℓ₁ * L
                        · exact ⟨ℓ₂, h21, by linarith, by linarith⟩
                        · exact ⟨ℓ₁, h13, by linarith, h12⟩
                      obtain ⟨ℓ, hl1, hl2, hl3⟩ := hE
                      obtain ⟨H', R', hf', hR', hl', hc'⟩ := ih (k + 1) (by omega) 0 0 le_rfl
                        (by rw [hPk]; linarith) (by intro ℓ' h; linarith [h.1, h.2])
                      try rw [← hM] at hf'
                      try rw [← hM] at hc'
                      obtain ⟨R'', hf'', hR'', hc''⟩ := hclose H' R' hR' (by linarith)
                      have hrest := htri 0 a M
                      have hbad' : IsBad d δ A k θ := ⟨ℓ₂, h21, h22⟩
                      by_cases hfour : δ < d a ∧ IsFourCopies d δ A k θ
                      · have htk : term k = 2 * c 0 a + 2 * c 0 a := by
                          simp only [htermdef, ← ha, if_pos hbad', if_pos hfour]
                        refine ⟨[], [a] :: R'', ?_, ?_, ?_, ?_⟩
                        · simp [hf'', ← hf']
                        · intro L' hL'
                          rcases List.mem_cons.1 hL' with rfl | hL'
                          · exact ⟨by simp, by simp [load]; linarith⟩
                          · exact hR'' L' hL'
                        · simp [load]; linarith
                        · rw [htk]
                          simp only [List.map_cons, List.sum_cons, hc'', List.nil_append, List.cons_append,
                            List.zipWith_cons_cons, List.sum_cons, List.zipWith_nil_right, List.sum_nil, hrc]
                          have := hc.triangle x 0 a
                          linarith
                      · have htk : term k = 2 * c 0 a + 0 := by
                          simp only [htermdef, ← ha, if_pos hbad', if_neg hfour]
                        refine ⟨[a], R'', ?_, hR'', ?_, ?_⟩
                        · simp [hf'', ← hf']
                        · simp only [load, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
                          by_cases hsm : d a ≤ δ
                          · linarith
                          · push_neg at hsm
                            have hnf : ¬ IsFourCopies d δ A k θ := fun h => hfour ⟨hsm, h⟩
                            have : ¬ (θ + ℓ * L ≤ P (k + 1) - δ) := fun h => hnf ⟨ℓ, hl1, h⟩
                            push_neg at this
                            rw [hPk] at this
                            linarith
                        · rw [htk, hc'']
                          simp only [List.cons_append, List.nil_append, List.zipWith_cons_cons,
                            List.zipWith_nil_right, List.sum_cons, List.sum_nil] at *
                          linarith
                    · have htk := hterm0 k
                      obtain ⟨H', R', hf', hR', hl', hc'⟩ := ih (k + 1) (by omega) a (lam + d a) (by linarith)
                        (by rw [hPk]; linarith) (by
                          intro ℓ' h
                          rw [hPk] at h
                          by_cases h' : θ + ℓ' * L ≤ P k
                          · exact hno ℓ' ⟨by linarith [h.1], h'⟩
                          · push_neg at h'
                            exact hbad ⟨ℓ', h', by show θ + ℓ' * L ≤ P (k + 1); rw [hPk]; linarith [h.2]⟩)
                      try rw [← hM] at hf'
                      try rw [← hM] at hc'
                      refine ⟨a :: H', R', ?_, hR', ?_, ?_⟩
                      · simp [hf']
                      · simp only [load, List.map_cons, List.sum_cons] at hl' ⊢
                        linarith
                      · simp only [List.cons_append, List.zipWith_cons_cons, List.sum_cons]
                        linarith
                obtain ⟨H, R, hf, hR, hl, hcst⟩ := key m 0 (by omega) 0 0 le_rfl (by rw [hP0]; simp)
                  (by intro ℓ h; rw [hP0] at h; linarith [h.1, h.2])
                obtain ⟨R'', hf'', hR'', hc''⟩ := hclose H R hR (by linarith)
                have hsplit : IsConsecutiveSplit d A R'' := ⟨by rw [hf'', hf]; simp, hR''⟩
                have hbdd : BddBelow {t | ∃ R, IsConsecutiveSplit d A R ∧ t = SupplyChainTheory.solutionCost c R} := by
                  refine ⟨0, ?_⟩
                  rintro _ ⟨R', -, rfl⟩
                  unfold SupplyChainTheory.solutionCost
                  apply List.sum_nonneg
                  intro y hy
                  obtain ⟨L', -, rfl⟩ := List.mem_map.1 hy
                  rw [hrc]; exact hZnn 0 L'
                calc bestSplit c d A ≤ SupplyChainTheory.solutionCost c R'' := csInf_le hbdd ⟨R'', hsplit, rfl⟩
                  _ ≤ _ := by
                    unfold SupplyChainTheory.solutionCost
                    rw [hc'', hrc A]
                    simp only [List.drop_zero] at hcst
                    have : addedCost c d δ A θ = ∑ i ∈ Finset.Ico 0 m, term i := by
                      unfold addedCost
                      rw [Finset.range_eq_Ico]
                    rw [this]
                    linarith
              have P2 : ∀ (A : List (Fin (n + 1))), (∀ v ∈ A, 0 < d v ∧ d v ≤ 1) → ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 - δ ∧
                  addedCost c d δ A θ ≤ ∑ i ∈ Finset.range A.length, (fun v => if d v ≤ δ then 2 * d v * c 0 v / (1 - δ) else 2 * c 0 v * (2 * d v - δ) / (1 - δ)) (A.getD i 0) := by
                intro A hA
                open MeasureTheory Set in
                ( have hL : 0 < 1 - δ := by linarith
                  have key : ∀ a b : ℝ, volume (Ico 0 (1 - δ) ∩ {θ : ℝ | ∃ ℓ : ℕ, a < θ + (ℓ : ℝ) * (1 - δ) ∧
                      θ + (ℓ : ℝ) * (1 - δ) ≤ b}) ≤ ENNReal.ofReal (b - a) := by
                    intro a b
                    have hsub : Ico 0 (1 - δ) ∩ {θ : ℝ | ∃ ℓ : ℕ, a < θ + (ℓ : ℝ) * (1 - δ) ∧
                        θ + (ℓ : ℝ) * (1 - δ) ≤ b} ⊆ ⋃ ℓ : ℕ, (fun θ => θ + (ℓ : ℝ) * (1 - δ)) ⁻¹'
                          (Ico ((ℓ : ℝ) * (1 - δ)) ((ℓ : ℝ) * (1 - δ) + (1 - δ)) ∩ Ioc a b) := by
                      rintro θ ⟨⟨h0, h1⟩, ℓ, h2, h3⟩
                      refine mem_iUnion.2 ⟨ℓ, ?_⟩
                      simp only [mem_preimage, mem_inter_iff, mem_Ico, mem_Ioc]
                      exact ⟨⟨by linarith, by linarith⟩, h2, h3⟩
                    have hdisj : Pairwise (Function.onFun Disjoint fun ℓ : ℕ =>
                        Ico ((ℓ : ℝ) * (1 - δ)) ((ℓ : ℝ) * (1 - δ) + (1 - δ)) ∩ Ioc a b) := by
                      intro i j hij
                      simp only [Function.onFun]
                      rw [Set.disjoint_left]
                      rintro y ⟨⟨h1, h2⟩, _⟩ ⟨⟨h3, h4⟩, _⟩
                      rcases lt_or_gt_of_ne hij with h | h
                      · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
                        nlinarith
                      · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
                        nlinarith
                    calc _ ≤ volume (⋃ ℓ : ℕ, (fun θ => θ + (ℓ : ℝ) * (1 - δ)) ⁻¹'
                          (Ico ((ℓ : ℝ) * (1 - δ)) ((ℓ : ℝ) * (1 - δ) + (1 - δ)) ∩ Ioc a b)) := measure_mono hsub
                      _ ≤ ∑' ℓ : ℕ, volume ((fun θ => θ + (ℓ : ℝ) * (1 - δ)) ⁻¹'
                          (Ico ((ℓ : ℝ) * (1 - δ)) ((ℓ : ℝ) * (1 - δ) + (1 - δ)) ∩ Ioc a b)) := measure_iUnion_le _
                      _ = ∑' ℓ : ℕ, volume (Ico ((ℓ : ℝ) * (1 - δ)) ((ℓ : ℝ) * (1 - δ) + (1 - δ)) ∩ Ioc a b) := by
                          congr 1; ext ℓ; exact measure_preimage_add_right _ _ _
                      _ ≤ volume (⋃ ℓ : ℕ, Ico ((ℓ : ℝ) * (1 - δ)) ((ℓ : ℝ) * (1 - δ) + (1 - δ)) ∩ Ioc a b) :=
                          tsum_meas_le_meas_iUnion_of_disjoint _ (fun _ => measurableSet_Ico.inter measurableSet_Ioc) hdisj
                      _ ≤ volume (Ioc a b) := measure_mono (iUnion_subset fun _ => inter_subset_right)
                      _ = ENNReal.ofReal (b - a) := Real.volume_Ioc
                  have hmeas : ∀ a b : ℝ, MeasurableSet {θ : ℝ | ∃ ℓ : ℕ, a < θ + (ℓ : ℝ) * (1 - δ) ∧
                      θ + (ℓ : ℝ) * (1 - δ) ≤ b} := by
                    intro a b
                    have : {θ : ℝ | ∃ ℓ : ℕ, a < θ + (ℓ : ℝ) * (1 - δ) ∧ θ + (ℓ : ℝ) * (1 - δ) ≤ b} =
                        ⋃ ℓ : ℕ, ({θ : ℝ | a < θ + (ℓ : ℝ) * (1 - δ)} ∩ {θ | θ + (ℓ : ℝ) * (1 - δ) ≤ b}) := by
                      ext θ; simp
                    rw [this]
                    exact MeasurableSet.iUnion fun ℓ =>
                      (measurableSet_lt measurable_const (measurable_id.add_const _)).inter
                        (measurableSet_le (measurable_id.add_const _) measurable_const)
                  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ → Set ℝ, ∀ a b, G a b = {θ : ℝ | ∃ ℓ : ℕ,
                      a < θ + (ℓ : ℝ) * (1 - δ) ∧ θ + (ℓ : ℝ) * (1 - δ) ≤ b} := ⟨_, fun _ _ => rfl⟩
                  obtain ⟨x, hx⟩ : ∃ x : ℕ → ℝ, ∀ i, x i = 2 * c 0 (A.getD i 0) := ⟨_, fun _ => rfl⟩
                  obtain ⟨y, hy⟩ : ∃ y : ℕ → ℝ, ∀ i, y i =
                      if δ < d (A.getD i 0) then 2 * c 0 (A.getD i 0) else 0 := ⟨_, fun _ => rfl⟩
                  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, ∀ θ, g θ = ∑ i ∈ Finset.range A.length,
                      ((G (prefixLoad d A i) (prefixLoad d A (i + 1))).indicator (fun _ => x i) θ +
                       (G (prefixLoad d A i) (prefixLoad d A (i + 1) - δ)).indicator (fun _ => y i) θ) :=
                    ⟨_, fun _ => rfl⟩
                  have hfg : ∀ θ, addedCost c d δ A θ = g θ := by
                    intro θ
                    rw [hg]
                    unfold addedCost
                    refine Finset.sum_congr rfl fun i _ => ?_
                    have m1 : θ ∈ G (prefixLoad d A i) (prefixLoad d A (i + 1)) ↔ IsBad d δ A i θ := by
                      rw [hG]; exact Iff.rfl
                    have m2 : θ ∈ G (prefixLoad d A i) (prefixLoad d A (i + 1) - δ) ↔
                        IsFourCopies d δ A i θ := by
                      rw [hG]; exact Iff.rfl
                    rw [hx, hy]
                    classical
                    simp only [Set.indicator_apply, m1, m2]
                    by_cases h1 : IsBad d δ A i θ <;> by_cases h2 : IsFourCopies d δ A i θ <;>
                      by_cases h3 : δ < d (A.getD i 0) <;>
                      simp only [h1, h2, h3, and_true, and_false, true_and, false_and, ↓reduceIte]
                  have hP : ∀ i < A.length, prefixLoad d A (i + 1) = prefixLoad d A i + d (A.getD i 0) := by
                    intro i hi
                    unfold prefixLoad load
                    rw [List.take_add_one, List.map_append, List.sum_append]
                    simp [List.getElem?_eq_getElem hi]
                  have hdA : ∀ i < A.length, 0 < d (A.getD i 0) ∧ d (A.getD i 0) ≤ 1 := by
                    intro i hi
                    rw [List.getD_eq_getElem _ _ hi]
                    exact hA _ (List.getElem_mem hi)
                  have hx0 : ∀ i, 0 ≤ x i := fun i => by rw [hx]; linarith [hc.nonneg 0 (A.getD i 0)]
                  have hmG : ∀ a b, MeasurableSet (G a b) := fun a b => by rw [hG]; exact hmeas a b
                  have hintI : ∀ a b (r : ℝ), Integrable ((G a b).indicator (fun _ => r))
                      (volume.restrict (Ico 0 (1 - δ))) := fun a b r =>
                    (integrableOn_const (C := r) (by simp)).indicator (hmG a b)
                  have hbound : ∀ a b (r : ℝ), 0 ≤ r → a ≤ b →
                      ∫ θ in Ico 0 (1 - δ), (G a b).indicator (fun _ => r) θ ≤ r * (b - a) := by
                    intro a b r hr hab
                    rw [integral_indicator_const _ (hmG a b), smul_eq_mul, Measure.real,
                      Measure.restrict_apply (hmG a b), inter_comm, mul_comm]
                    refine mul_le_mul_of_nonneg_left ?_ hr
                    exact ENNReal.toReal_le_of_le_ofReal (sub_nonneg.2 hab) (by rw [hG]; exact key a b)
                  have hgint : Integrable g (volume.restrict (Ico 0 (1 - δ))) := by
                    have : g = fun θ => ∑ i ∈ Finset.range A.length,
                      ((G (prefixLoad d A i) (prefixLoad d A (i + 1))).indicator (fun _ => x i) θ +
                       (G (prefixLoad d A i) (prefixLoad d A (i + 1) - δ)).indicator (fun _ => y i) θ) :=
                      funext hg
                    rw [this]
                    exact integrable_finsetSum _ fun i _ => (hintI _ _ _).add (hintI _ _ _)
                  have hint : ∫ θ in Ico 0 (1 - δ), g θ ≤ ∑ i ∈ Finset.range A.length,
                      (x i * d (A.getD i 0) + y i * (d (A.getD i 0) - δ)) := by
                    simp_rw [hg]
                    have hIi : ∀ i, Integrable (fun θ =>
                        (G (prefixLoad d A i) (prefixLoad d A (i + 1))).indicator (fun _ => x i) θ +
                        (G (prefixLoad d A i) (prefixLoad d A (i + 1) - δ)).indicator (fun _ => y i) θ)
                        (volume.restrict (Ico 0 (1 - δ))) := fun i => (hintI _ _ _).add (hintI _ _ _)
                    rw [integral_finsetSum _ fun i _ => hIi i]
                    refine Finset.sum_le_sum fun i hi => ?_
                    have hi' := Finset.mem_range.1 hi
                    rw [integral_add (hintI _ _ _) (hintI _ _ _)]
                    have h1 := hbound (prefixLoad d A i) (prefixLoad d A (i + 1)) (x i) (hx0 i)
                      (by rw [hP i hi']; linarith [(hdA i hi').1])
                    have h1' : x i * (prefixLoad d A (i + 1) - prefixLoad d A i) = x i * d (A.getD i 0) := by
                      rw [hP i hi']; ring
                    refine add_le_add (by linarith) ?_
                    by_cases hb : δ < d (A.getD i 0)
                    · have h2 := hbound (prefixLoad d A i) (prefixLoad d A (i + 1) - δ) (y i)
                        (by rw [hy, if_pos hb]; exact hx0 i |>.trans_eq (hx i))
                        (by rw [hP i hi']; linarith)
                      have h2' : y i * (prefixLoad d A (i + 1) - δ - prefixLoad d A i) =
                          y i * (d (A.getD i 0) - δ) := by
                        rw [hP i hi']; ring
                      linarith
                    · rw [hy, if_neg hb]; simp
                  have hsumeq : ∑ i ∈ Finset.range A.length,
                      (x i * d (A.getD i 0) + y i * (d (A.getD i 0) - δ)) = (1 - δ) *
                      ∑ i ∈ Finset.range A.length,
                        (fun v => if d v ≤ δ then 2 * d v * c 0 v / (1 - δ)
                          else 2 * c 0 v * (2 * d v - δ) / (1 - δ)) (A.getD i 0) := by
                    rw [Finset.mul_sum]
                    refine Finset.sum_congr rfl fun i _ => ?_
                    rw [hx, hy]
                    by_cases hb : d (A.getD i 0) ≤ δ
                    · dsimp only; rw [if_neg (not_lt.2 hb), if_pos hb]; field_simp; ring
                    · dsimp only; rw [if_pos (not_le.1 hb), if_neg hb]; field_simp; ring
                  -- finitely many values
                  classical
                  have hfin : (g '' Ico 0 (1 - δ)).Finite := by
                    refine (Finset.finite_toSet
                      (((Finset.range A.length).powerset ×ˢ (Finset.range A.length).powerset).image
                        (fun ST : Finset ℕ × Finset ℕ => ∑ i ∈ Finset.range A.length,
                          ((if i ∈ ST.1 then x i else 0) + (if i ∈ ST.2 then y i else 0))))).subset ?_
                    rintro _ ⟨θ, _, rfl⟩
                    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product,
                      Finset.mem_powerset, Prod.exists]
                    refine ⟨(Finset.range A.length).filter
                        (fun i => θ ∈ G (prefixLoad d A i) (prefixLoad d A (i + 1))),
                      (Finset.range A.length).filter
                        (fun i => θ ∈ G (prefixLoad d A i) (prefixLoad d A (i + 1) - δ)),
                      ⟨Finset.filter_subset _ _, Finset.filter_subset _ _⟩, ?_⟩
                    rw [hg]
                    refine Finset.sum_congr rfl fun i hi => ?_
                    simp only [Finset.mem_filter, hi, true_and, Set.indicator_apply]
                  have hne : (g '' Ico 0 (1 - δ)).Nonempty := ⟨g 0, 0, ⟨le_refl _, hL⟩, rfl⟩
                  obtain ⟨_, ⟨θ, hθ, rfl⟩, hmin⟩ := Set.exists_min_image _ id hfin hne
                  refine ⟨θ, hθ.1, hθ.2, ?_⟩
                  rw [hfg]
                  have hlow : ∫ _ in Ico 0 (1 - δ), g θ ≤ ∫ t in Ico 0 (1 - δ), g t :=
                    setIntegral_mono_on (integrableOn_const (by simp)) hgint measurableSet_Ico
                      (fun t ht => hmin _ ⟨t, ht, rfl⟩)
                  rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ico,
                    ENNReal.toReal_ofReal (by linarith)] at hlow
                  have := hlow.trans (hint.trans_eq hsumeq)
                  exact le_of_mul_le_mul_left (by linarith) hL)

              · intro δ' hδ'0 hδ'1
                have hcostnn : ∀ R : List (List (Fin (n + 1))), 0 ≤ SupplyChainTheory.solutionCost c R := by
                  intro R
                  unfold SupplyChainTheory.solutionCost
                  apply List.sum_nonneg
                  intro x hx'
                  obtain ⟨L, -, rfl⟩ := List.mem_map.1 hx'
                  unfold SupplyChainTheory.routeCost SupplyChainTheory.closedLength
                  apply List.sum_nonneg
                  intro y hy
                  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hy
                  rw [List.getElem_zipWith]
                  exact hc.nonneg _ _
                have hp0 : ∀ T ∈ configTours d δ, 0 ≤ roundProb (Real.log 2) xstar T := by
                  intro T hT
                  unfold roundProb
                  exact le_min zero_le_one (mul_nonneg (Real.log_nonneg (by norm_num)) (hx.1.1 T hT))
                have hp1 : ∀ T, roundProb (Real.log 2) xstar T ≤ 1 := fun T => min_le_left _ _
                have hw0 : ∀ S ∈ (configTours d δ).powerset, 0 ≤ sampleWeight d δ (Real.log 2) xstar S := by
                  intro S hS
                  rw [Finset.mem_powerset] at hS
                  unfold sampleWeight
                  apply mul_nonneg
                  · exact Finset.prod_nonneg fun T hT => hp0 T (hS hT)
                  · exact Finset.prod_nonneg fun T _ => sub_nonneg.2 (hp1 T)
                have hwsum : ∑ S ∈ (configTours d δ).powerset, sampleWeight d δ (Real.log 2) xstar S = 1 := by
                  classical
                  unfold sampleWeight
                  rw [← Finset.prod_add]
                  simp
                have hexpB : expect d δ (Real.log 2) xstar
                    (fun S => min (alg2Cost c d tour S) (SupplyChainTheory.solutionCost c (B δ'))) ≤
                    SupplyChainTheory.solutionCost c (B δ') := by
                  unfold expect
                  calc _ ≤ ∑ S ∈ (configTours d δ).powerset, sampleWeight d δ (Real.log 2) xstar S *
                        SupplyChainTheory.solutionCost c (B δ') := by
                        apply Finset.sum_le_sum
                        intro S hS
                        exact mul_le_mul_of_nonneg_left (min_le_right _ _) (hw0 S hS)
                    _ = _ := by rw [← Finset.sum_mul, hwsum, one_mul]
                have hexpA : expect d δ (Real.log 2) xstar
                    (fun S => min (alg2Cost c d tour S) (SupplyChainTheory.solutionCost c (B δ'))) ≤
                    ∑ S ∈ (configTours d δ).powerset, sampleWeight d δ (Real.log 2) xstar S *
                      alg2Cost c d tour S := by
                  unfold expect
                  apply Finset.sum_le_sum
                  intro S hS
                  exact mul_le_mul_of_nonneg_left (min_le_left _ _) (hw0 S hS)
                classical
                -- route cost in path form
                have hrc : ∀ L : List (Fin (n + 1)), SupplyChainTheory.routeCost c L =
                    (List.zipWith c (0 :: L) (L ++ [0])).sum := by
                  intro L
                  simp [SupplyChainTheory.routeCost, SupplyChainTheory.closedLength]
                have htri : ∀ (a x : Fin (n + 1)) (M : List (Fin (n + 1))),
                    (List.zipWith c (a :: M) (M ++ [0])).sum ≤
                      c a x + (List.zipWith c (x :: M) (M ++ [0])).sum := by
                  intro a x M
                  cases M with
                  | nil => simpa using hc.triangle a 0 x
                  | cons y M =>
                    simp only [List.cons_append, List.zipWith_cons_cons, List.sum_cons]
                    have := hc.triangle a y x
                    linarith
                have hfilt : ∀ (p : Fin (n + 1) → Bool) (L : List (Fin (n + 1))) (a : Fin (n + 1)),
                    (List.zipWith c (a :: L.filter p) (L.filter p ++ [0])).sum ≤
                      (List.zipWith c (a :: L) (L ++ [0])).sum := by
                  intro p L
                  induction L with
                  | nil => intro a; simp
                  | cons x L ih =>
                    intro a
                    by_cases hpx : p x = true
                    · rw [List.filter_cons_of_pos hpx]
                      simp only [List.cons_append, List.zipWith_cons_cons, List.sum_cons]
                      have := ih x
                      linarith
                    · rw [List.filter_cons_of_neg hpx]
                      have h1 := htri a x (L.filter p)
                      have h2 := ih x
                      simp only [List.cons_append, List.zipWith_cons_cons, List.sum_cons]
                      linarith
                have hload : ∀ (p : Fin (n + 1) → Bool) (L : List (Fin (n + 1))),
                    (∀ v ∈ L, v ∈ clients n) → load d (L.filter p) ≤ load d L := by
                  intro p L hL
                  unfold load
                  apply List.Sublist.sum_le_sum ((List.filter_sublist).map d)
                  intro a ha
                  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 ha
                  have := hL v hv
                  simp [clients] at this
                  exact (hd v this).1.le
                refine ⟨?_, ?_⟩
                · intro S hS
                  by_cases hle : SupplyChainTheory.solutionCost c (B δ') ≤ alg2Cost c d tour S
                  · exact ⟨B δ', hB δ' hδ'0 hδ'1, le_min hle le_rfl⟩
                  · rw [not_le] at hle
                    classical
                    -- shortcut induction
                    have hmain : ∀ (R0 : List (List (Fin (n + 1)))),
                        (∀ L ∈ R0, L ≠ [] ∧ (0 : Fin (n + 1)) ∉ L ∧ load d L ≤ 1) → R0.flatten.Nodup →
                        ∀ Ts : List (List (Fin (n + 1))),
                        (∀ T ∈ Ts, T.Nodup ∧ load d T ≤ 1 ∧ ∀ v ∈ T, v ∈ clients n) →
                        ∃ R : List (List (Fin (n + 1))),
                          (∀ L ∈ R, L ≠ [] ∧ (0 : Fin (n + 1)) ∉ L ∧ load d L ≤ 1) ∧ R.flatten.Nodup ∧
                          (∀ v, v ∈ R.flatten ↔ (v ∈ R0.flatten ∨ ∃ T ∈ Ts, v ∈ T)) ∧
                          SupplyChainTheory.solutionCost c R ≤
                            (Ts.map (SupplyChainTheory.routeCost c)).sum + SupplyChainTheory.solutionCost c R0 := by
                      intro R0 hR0 hR0n Ts
                      induction Ts with
                      | nil => intro _; exact ⟨R0, hR0, hR0n, by simp, by simp⟩
                      | cons T Ts ih =>
                        intro hTs
                        obtain ⟨R', h1, h2, h3, h4⟩ := ih (fun T' hT' => hTs T' (by simp [hT']))
                        obtain ⟨hTn, hTl, hTc⟩ := hTs T (by simp)
                        have hTnn : 0 ≤ SupplyChainTheory.routeCost c T := by
                          have := hcostnn [T]
                          rwa [SupplyChainTheory.solutionCost, List.map_singleton, List.sum_singleton] at this
                        set T' := T.filter (fun v => decide (v ∉ R'.flatten)) with hT'
                        by_cases hTe : T' = []
                        · refine ⟨R', h1, h2, ?_, ?_⟩
                          · intro v
                            rw [h3 v]
                            constructor
                            · rintro (h | ⟨T'', hT'', hv⟩)
                              · exact Or.inl h
                              · exact Or.inr ⟨T'', by simp [hT''], hv⟩
                            · rintro (h | ⟨T'', hT'', hv⟩)
                              · exact Or.inl h
                              · simp only [List.mem_cons] at hT''
                                rcases hT'' with rfl | hT''
                                · by_contra hcon
                                  have hv' : v ∈ T' := by
                                    rw [hT', List.mem_filter]
                                    refine ⟨hv, ?_⟩
                                    have hnot : v ∉ R'.flatten := fun h => hcon ((h3 v).1 h)
                                    simpa only [decide_eq_true_eq] using hnot
                                  rw [hTe] at hv'
                                  simp at hv'
                                · exact Or.inr ⟨T'', hT'', hv⟩
                          · simp only [List.map_cons, List.sum_cons]
                            linarith
                        · refine ⟨T' :: R', ?_, ?_, ?_, ?_⟩
                          · intro L hL
                            simp only [List.mem_cons] at hL
                            rcases hL with rfl | hL
                            · refine ⟨hTe, ?_, le_trans (hload _ _ hTc) hTl⟩
                              intro h0
                              have := hTc 0 (List.mem_of_mem_filter h0)
                              simp [clients] at this
                            · exact h1 L hL
                          · rw [List.flatten_cons, List.nodup_append]
                            refine ⟨hTn.filter _, h2, ?_⟩
                            intro a ha b hb hab
                            subst hab
                            have := (List.mem_filter.1 ha).2
                            simp only [decide_eq_true_eq] at this
                            exact this hb
                          · intro v
                            rw [List.flatten_cons, List.mem_append, h3 v]
                            constructor
                            · rintro (h | h | ⟨T'', hT'', hv⟩)
                              · exact Or.inr ⟨T, by simp, List.mem_of_mem_filter h⟩
                              · exact Or.inl h
                              · exact Or.inr ⟨T'', by simp [hT''], hv⟩
                            · rintro (h | ⟨T'', hT'', hv⟩)
                              · exact Or.inr (Or.inl h)
                              · simp only [List.mem_cons] at hT''
                                rcases hT'' with rfl | hT''
                                · by_cases hin : v ∈ R'.flatten
                                  · exact Or.inr ((h3 v).1 hin)
                                  · exact Or.inl (List.mem_filter.2 ⟨hv, by simpa using hin⟩)
                                · exact Or.inr (Or.inr ⟨T'', hT'', hv⟩)
                          · simp only [SupplyChainTheory.solutionCost, List.map_cons, List.sum_cons] at h4 ⊢
                            have : SupplyChainTheory.routeCost c T' ≤ SupplyChainTheory.routeCost c T := by
                              rw [hrc, hrc]; exact hfilt _ T 0
                            linarith
                    -- finiteness of splits
                    have hlenle : ∀ R : List (List (Fin (n + 1))), (∀ L ∈ R, L ≠ []) →
                        R.length ≤ R.flatten.length := by
                      intro R h
                      induction R with
                      | nil => simp
                      | cons a R ih =>
                        simp only [List.length_cons, List.flatten_cons, List.length_append]
                        have := List.length_pos_iff.2 (h a (by simp))
                        have := ih (fun L hL => h L (by simp [hL]))
                        omega
                    have hinj : ∀ (R1 R2 : List (List (Fin (n + 1)))), R1.flatten = R2.flatten →
                        R1.map List.length = R2.map List.length → R1 = R2 := by
                      intro R1
                      induction R1 with
                      | nil =>
                        intro R2 _ h
                        cases R2 with
                        | nil => rfl
                        | cons b R2 => simp only [List.map_nil, List.map_cons] at h; exact absurd h.symm (List.cons_ne_nil _ _)
                      | cons a R1 ih =>
                        intro R2 h1 h2
                        cases R2 with
                        | nil => simp at h2
                        | cons b R2 =>
                          simp only [List.map_cons, List.cons.injEq] at h2
                          simp only [List.flatten_cons] at h1
                          obtain ⟨hab, hR⟩ := List.append_inj h1 h2.1
                          rw [hab, ih R2 hR h2.2]
                    have hfin : ∀ A : List (Fin (n + 1)),
                        {R : List (List (Fin (n + 1))) | R.flatten = A ∧ ∀ L ∈ R, L ≠ []}.Finite := by
                      intro A
                      apply Set.Finite.of_finite_image (f := fun R => R.map List.length)
                      · apply ((List.finite_length_le (Fin (A.length + 1)) A.length).image
                          (List.map Fin.val)).subset
                        rintro _ ⟨R, ⟨hR1, hR2⟩, rfl⟩
                        have hLle : ∀ L ∈ R, L.length ≤ A.length := by
                          intro L hL
                          rw [← hR1, List.length_flatten]
                          exact List.le_sum_of_mem (List.mem_map_of_mem hL)
                        refine ⟨R.map (fun L => (⟨min L.length A.length, by omega⟩ : Fin (A.length + 1))),
                          ?_, ?_⟩
                        · simp only [Set.mem_setOf_eq, List.length_map]
                          have := hlenle R hR2
                          rw [hR1] at this
                          exact this
                        · simp only [List.map_map]
                          apply List.map_congr_left
                          intro L hL
                          simp [hLle L hL]
                      · intro R1 h1 R2 h2 heq
                        exact hinj R1 R2 (h1.1.trans h2.1.symm) heq
                    -- attainment of bestSplit
                    have hsplit : ∀ U ⊆ clients n, ∃ R0, IsConsecutiveSplit d (tour U) R0 ∧
                        bestSplit c d (tour U) = SupplyChainTheory.solutionCost c R0 := by
                      intro U hU
                      have hne : {t | ∃ R, IsConsecutiveSplit d (tour U) R ∧
                          t = SupplyChainTheory.solutionCost c R}.Nonempty := by
                        refine ⟨_, (tour U).map (fun v => [v]), ⟨?_, ?_⟩, rfl⟩
                        · show ((tour U).map (fun v => [v])).flatten = tour U
                          induction (tour U) with
                          | nil => rfl
                          | cons a l ih => simp only [List.map_cons, List.flatten_cons, ih]; rfl
                        · intro L hL
                          obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hL
                          refine ⟨by simp, ?_⟩
                          have : v ∈ clients n := hU (((htour U hU).2 v).1 hv)
                          simp [clients] at this
                          simpa [load] using (hd v this).2
                      have hfi : {t | ∃ R, IsConsecutiveSplit d (tour U) R ∧
                          t = SupplyChainTheory.solutionCost c R}.Finite := by
                        apply ((hfin (tour U)).image (SupplyChainTheory.solutionCost c)).subset
                        rintro _ ⟨R, hR, rfl⟩
                        exact ⟨R, ⟨hR.1, fun L hL => (hR.2 L hL).1⟩, rfl⟩
                      obtain ⟨R0, hR0, hR0e⟩ := hne.csInf_mem hfi
                      exact ⟨R0, hR0, hR0e⟩
                    have hUsub : uncovered n S ⊆ clients n := Finset.sdiff_subset
                    obtain ⟨R0, ⟨hR0f, hR0L⟩, hR0c⟩ := hsplit _ hUsub
                    have hTs : ∀ T ∈ S.toList, T.Nodup ∧ load d T ≤ 1 ∧ ∀ v ∈ T, v ∈ clients n := by
                      intro T hT
                      rw [Finset.mem_toList] at hT
                      have hT' := Finset.mem_powerset.1 hS hT
                      unfold configTours at hT'
                      simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and,
                        Function.Embedding.coe_subtype] at hT'
                      obtain ⟨⟨l, rfl⟩, -, hall, hl⟩ := hT'
                      exact ⟨l.2, hl, fun v hv => (Finset.mem_filter.1 (hall v hv)).1⟩
                    have hR0' : ∀ L ∈ R0, L ≠ [] ∧ (0 : Fin (n + 1)) ∉ L ∧ load d L ≤ 1 := by
                      intro L hL
                      refine ⟨(hR0L L hL).1, ?_, (hR0L L hL).2⟩
                      intro h0
                      have h0' : (0 : Fin (n + 1)) ∈ R0.flatten := List.mem_flatten.2 ⟨L, hL, h0⟩
                      rw [hR0f] at h0'
                      have := hUsub (((htour _ hUsub).2 0).1 h0')
                      simp [clients] at this
                    have hR0n : R0.flatten.Nodup := by rw [hR0f]; exact (htour _ hUsub).1
                    obtain ⟨R, h1, h2, h3, h4⟩ := hmain R0 hR0' hR0n S.toList hTs
                    refine ⟨R, ⟨h1, h2, ?_⟩, ?_⟩
                    · intro v
                      rw [h3 v, hR0f, (htour _ hUsub).2 v]
                      simp only [uncovered, covered, Finset.mem_sdiff, Finset.mem_biUnion,
                        List.mem_toFinset, Finset.mem_toList]
                      constructor
                      · rintro (⟨h, -⟩ | ⟨T, hT, hv⟩)
                        · exact h
                        · exact (hTs T (Finset.mem_toList.2 hT)).2.2 v hv
                      · intro hv
                        by_cases hcov : ∃ T ∈ S, v ∈ T
                        · exact Or.inr hcov
                        · exact Or.inl ⟨hv, hcov⟩
                    · rw [min_eq_left hle.le]
                      unfold alg2Cost
                      rw [hR0c, ← Finset.sum_map_toList]
                      exact h4
                · intro R hR
                  by_cases hrad : (1 - δ') * SupplyChainTheory.solutionCost c R ≤ radial c d (clients n)
                  · calc _ ≤ SupplyChainTheory.solutionCost c (B δ') := hexpB
                      _ ≤ (3 + f δ') * SupplyChainTheory.solutionCost c R := hBcost δ' hδ'0 hδ'1 R hR hrad
                      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (hcostnn R)
                  · -- Remaining: the paper's main analysis (LP ≤ OPT, coverage probability, Lemma 7 tiling).
                    rw [not_le] at hrad
                    set J := configTours d δ with hJ
                    set p := roundProb (Real.log 2) xstar with hp
                    -- general product-weight identities
                    have hgen : ∀ (J' : Finset (List (Fin (n + 1)))) (g : List (Fin (n + 1)) → ℝ),
                        (∑ S ∈ J'.powerset, (∏ T ∈ S, p T) * ∏ T ∈ J' \ S, (1 - p T)) = 1 ∧
                        (∑ S ∈ J'.powerset, (∏ T ∈ S, p T) * (∏ T ∈ J' \ S, (1 - p T)) * ∑ T ∈ S, g T)
                          = ∑ T ∈ J', p T * g T := by
                      intro J' g
                      induction J' using Finset.induction_on with
                      | empty => simp
                      | insert a J0 ha ih =>
                        obtain ⟨ih1, ih2⟩ := ih
                        rw [Finset.sum_powerset_insert ha, Finset.sum_powerset_insert ha]
                        have hS1 : ∀ S ∈ J0.powerset, insert a J0 \ S = insert a (J0 \ S) := by
                          intro S hS
                          have : a ∉ S := fun h => ha (Finset.mem_powerset.1 hS h)
                          ext x; simp only [Finset.mem_sdiff, Finset.mem_insert]
                          constructor
                          · rintro ⟨h1 | h1, h2⟩
                            · exact Or.inl h1
                            · exact Or.inr ⟨h1, h2⟩
                          · rintro (h1 | ⟨h1, h2⟩)
                            · subst h1; exact ⟨Or.inl rfl, this⟩
                            · exact ⟨Or.inr h1, h2⟩
                        have hS2 : ∀ S ∈ J0.powerset, insert a J0 \ insert a S = J0 \ S := by
                          intro S hS
                          ext x; simp only [Finset.mem_sdiff, Finset.mem_insert]
                          constructor
                          · rintro ⟨h1 | h1, h2⟩
                            · exact absurd (Or.inl h1) h2
                            · exact ⟨h1, fun h => h2 (Or.inr h)⟩
                          · rintro ⟨h1, h2⟩
                            refine ⟨Or.inr h1, ?_⟩
                            rintro (h | h)
                            · exact ha (h ▸ h1)
                            · exact h2 h
                        have hnS : ∀ S ∈ J0.powerset, a ∉ S := fun S hS h => ha (Finset.mem_powerset.1 hS h)
                        have hA : ∀ S ∈ J0.powerset, (∏ T ∈ S, p T) * ∏ T ∈ insert a J0 \ S, (1 - p T) =
                            (1 - p a) * ((∏ T ∈ S, p T) * ∏ T ∈ J0 \ S, (1 - p T)) := by
                          intro S hS
                          rw [hS1 S hS, Finset.prod_insert (fun h => ha (Finset.mem_sdiff.1 h).1)]; ring
                        have hB' : ∀ S ∈ J0.powerset, (∏ T ∈ insert a S, p T) * ∏ T ∈ insert a J0 \ insert a S, (1 - p T) =
                            p a * ((∏ T ∈ S, p T) * ∏ T ∈ J0 \ S, (1 - p T)) := by
                          intro S hS
                          rw [hS2 S hS, Finset.prod_insert (hnS S hS)]; ring
                        constructor
                        · rw [Finset.sum_congr rfl hA, Finset.sum_congr rfl hB', ← Finset.mul_sum, ← Finset.mul_sum, ih1]
                          ring
                        · rw [Finset.sum_insert ha]
                          have e : ∀ S ∈ J0.powerset, (1 - p a) * ((∏ T ∈ S, p T) * ∏ T ∈ J0 \ S, (1 - p T)) * ∑ T ∈ S, g T
                              + p a * ((∏ T ∈ S, p T) * ∏ T ∈ J0 \ S, (1 - p T)) * (g a + ∑ T ∈ S, g T)
                              = (∏ T ∈ S, p T) * (∏ T ∈ J0 \ S, (1 - p T)) * ∑ T ∈ S, g T
                                + p a * g a * ((∏ T ∈ S, p T) * ∏ T ∈ J0 \ S, (1 - p T)) := by
                            intro S hS; ring
                          have e2 : ∀ S ∈ J0.powerset,
                              (∏ T ∈ S, p T) * (∏ T ∈ insert a J0 \ S, (1 - p T)) * ∑ T ∈ S, g T
                              + (∏ T ∈ insert a S, p T) * (∏ T ∈ insert a J0 \ insert a S, (1 - p T)) *
                                  ∑ T ∈ insert a S, g T
                              = (∏ T ∈ S, p T) * (∏ T ∈ J0 \ S, (1 - p T)) * ∑ T ∈ S, g T
                                + p a * g a * ((∏ T ∈ S, p T) * ∏ T ∈ J0 \ S, (1 - p T)) := by
                            intro S hS
                            rw [hA S hS, hB' S hS, Finset.sum_insert (hnS S hS)]; exact e S hS
                          rw [← Finset.sum_add_distrib, Finset.sum_congr rfl e2, Finset.sum_add_distrib, ih2,
                            ← Finset.mul_sum, ih1]
                          ring
                    have hwdef : ∀ S, sampleWeight d δ (Real.log 2) xstar S =
                        (∏ T ∈ S, p T) * ∏ T ∈ J \ S, (1 - p T) := fun S => rfl
                    have hRc := hcostnn R
                    have hln : 0 < Real.log 2 := Real.log_pos (by norm_num)
                    -- LP ≤ OPT
                    have hLP : configCost c d δ xstar ≤ SupplyChainTheory.solutionCost c R := by
                      obtain ⟨hRL, hRn, hRmem⟩ := hR
                      letI : BEq (List (Fin (n + 1))) := instBEqOfDecidableEq
                      set filt : List (Fin (n + 1)) → List (Fin (n + 1)) :=
                        fun L => L.filter (fun v => decide (v ∈ bigIn d δ (clients n))) with hfiltdef
                      have hrcnn : ∀ T, 0 ≤ SupplyChainTheory.routeCost c T := fun T => by
                        have := hcostnn [T]; rwa [SupplyChainTheory.solutionCost, List.map_singleton, List.sum_singleton] at this
                      have hJmem : ∀ L ∈ R, filt L ≠ [] → filt L ∈ J := by
                        intro L hL hne
                        have hLn : L.Nodup := (List.nodup_flatten.1 hRn).1 L hL
                        have hLc : ∀ v ∈ L, v ∈ clients n := fun v hv =>
                          (hRmem v).1 (List.mem_flatten.2 ⟨L, hL, hv⟩)
                        rw [hJ]
                        simp only [configTours, Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and,
                          Function.Embedding.coe_subtype]
                        refine ⟨⟨⟨filt L, hLn.filter _⟩, rfl⟩, hne, ?_, le_trans (hload _ _ hLc) (hRL L hL).2.2⟩
                        intro v hv
                        simpa using (List.mem_filter.1 hv).2
                      set M := (R.map filt).filter (fun T => decide (T ≠ [])) with hM
                      have hMJ : ∀ T ∈ M, T ∈ J := by
                        intro T hT
                        rw [hM, List.mem_filter] at hT
                        obtain ⟨hT1, hT2⟩ := hT
                        obtain ⟨L, hL, rfl⟩ := List.mem_map.1 hT1
                        exact hJmem L hL (by simpa using hT2)
                      let y : List (Fin (n + 1)) → ℝ := fun T => (M.count T : ℝ)
                      have hyf : IsConfigFeasible d δ y := by
                        refine ⟨fun T _ => Nat.cast_nonneg _, ?_⟩
                        intro v hv
                        have hvc : v ∈ clients n := (Finset.mem_filter.1 hv).1
                        obtain ⟨L, hL, hvL⟩ := List.mem_flatten.1 ((hRmem v).2 hvc)
                        have hvf : v ∈ filt L := List.mem_filter.2 ⟨hvL, by simpa using hv⟩
                        have hne : filt L ≠ [] := List.ne_nil_of_mem hvf
                        have hTM : filt L ∈ M := by
                          rw [hM, List.mem_filter]
                          exact ⟨List.mem_map_of_mem hL, by simpa using hne⟩
                        have hmemJ : filt L ∈ J.filter (fun T => v ∈ T) :=
                          Finset.mem_filter.2 ⟨hJmem L hL hne, hvf⟩
                        calc (1 : ℝ) ≤ y (filt L) := by
                              show (1 : ℝ) ≤ (M.count (filt L) : ℝ)
                              exact_mod_cast Nat.succ_le_of_lt (List.count_pos_iff.2 hTM)
                          _ ≤ _ := Finset.single_le_sum (f := y) (fun T _ => Nat.cast_nonneg _) hmemJ
                      refine le_trans (hx.2 y hyf) ?_
                      unfold configCost
                      have hsub : M.toFinset ⊆ J := fun T hT => hMJ T (List.mem_toFinset.1 hT)
                      calc ∑ T ∈ J, SupplyChainTheory.routeCost c T * y T
                          = ∑ T ∈ J, M.count T • SupplyChainTheory.routeCost c T := by
                            apply Finset.sum_congr rfl; intro T _; rw [nsmul_eq_mul, mul_comm]
                        _ = ∑ T ∈ M.toFinset, M.count T • SupplyChainTheory.routeCost c T := by
                            symm
                            apply Finset.sum_subset hsub
                            intro T _ hT
                            rw [List.mem_toFinset] at hT
                            rw [List.count_eq_zero_of_not_mem hT, zero_smul]
                        _ = (M.map (SupplyChainTheory.routeCost c)).sum := by
                            rw [Finset.sum_list_map_count]
                        _ ≤ ((R.map filt).map (SupplyChainTheory.routeCost c)).sum := by
                            apply List.Sublist.sum_le_sum ((List.filter_sublist).map _)
                            intro a ha
                            obtain ⟨T, -, rfl⟩ := List.mem_map.1 ha
                            exact hrcnn T
                        _ ≤ _ := by
                            unfold SupplyChainTheory.solutionCost
                            rw [List.map_map]
                            apply List.sum_le_sum
                            intro L _
                            rw [Function.comp_apply, hrc, hrc]
                            exact hfilt _ L 0
                    have hE1 : ∑ S ∈ J.powerset, sampleWeight d δ (Real.log 2) xstar S *
                        ∑ T ∈ S, SupplyChainTheory.routeCost c T ≤
                          Real.log 2 * SupplyChainTheory.solutionCost c R := by
                      simp_rw [hwdef]
                      rw [(hgen J _).2]
                      calc _ ≤ ∑ T ∈ J, Real.log 2 * (SupplyChainTheory.routeCost c T * xstar T) := by
                            apply Finset.sum_le_sum
                            intro T hT
                            have h1 : p T ≤ Real.log 2 * xstar T := min_le_right _ _
                            have h2 : 0 ≤ SupplyChainTheory.routeCost c T := by
                              have := hcostnn [T]; rwa [SupplyChainTheory.solutionCost, List.map_singleton, List.sum_singleton] at this
                            nlinarith
                        _ = Real.log 2 * configCost c d δ xstar := by rw [configCost, Finset.mul_sum]
                        _ ≤ _ := mul_le_mul_of_nonneg_left hLP hln.le
                    have hE2 : ∑ S ∈ J.powerset, sampleWeight d δ (Real.log 2) xstar S *
                        bestSplit c d (tour (uncovered n S)) ≤
                          α * SupplyChainTheory.solutionCost c R + radial c d (clients n) / (1 - δ) := by
                      set h : Fin (n + 1) → ℝ := fun v => if d v ≤ δ then 2 * d v * c 0 v / (1 - δ)
                        else 2 * c 0 v * (2 * d v - δ) / (1 - δ) with hh
                      -- Lemma 7 (δ-tank tiling, averaged over the offset)
                      have hsplitB : ∀ U ⊆ clients n, bestSplit c d (tour U) ≤
                          SupplyChainTheory.routeCost c (tour U) + ∑ v ∈ U, h v := by
                        intro U hU
                        have hAv : ∀ v ∈ tour U, 0 < d v ∧ d v ≤ 1 := by
                          intro v hv
                          have hvU := ((htour U hU).2 v).1 hv
                          have hv0 : v ≠ 0 := by have := hU hvU; simpa [clients] using this
                          exact hd v hv0
                        obtain ⟨θ, hθ0, hθ1, hθ⟩ := P2 (tour U) hAv
                        have hθ' : addedCost c d δ (tour U) θ ≤ ∑ i ∈ Finset.range (tour U).length, h ((tour U).getD i 0) := hθ
                        have h1 := P1 (tour U) hAv θ hθ0 hθ1
                        have hlist : ∀ l : List (Fin (n + 1)), (l.map h).sum = ∑ i ∈ Finset.range l.length, h (l.getD i 0) := by
                          intro l
                          induction l with
                          | nil => simp
                          | cons a l ih =>
                            rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons, ih]
                            simp only [List.getD_cons_succ, List.getD_cons_zero]
                            ring
                        have hUeq : (tour U).toFinset = U := by
                          ext v; simp [(htour U hU).2 v]
                        have hconv : ∑ i ∈ Finset.range (tour U).length, h ((tour U).getD i 0) = ∑ v ∈ U, h v := by
                          rw [← hlist, ← List.sum_toFinset _ (htour U hU).1, hUeq]
                        linarith
                      -- the TSP part: α · tsp(U) ≤ α · cost R
                      have hα : ∀ U ⊆ clients n, SupplyChainTheory.routeCost c (tour U) ≤
                          α * SupplyChainTheory.solutionCost c R := by
                        obtain ⟨hRL, hRn, hRmem⟩ := hR
                        have hZnn : ∀ (a : Fin (n + 1)) (M : List (Fin (n + 1))),
                            0 ≤ (List.zipWith c (a :: M) (M ++ [0])).sum := by
                          intro a M
                          apply List.sum_nonneg
                          intro y hy
                          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hy
                          rw [List.getElem_zipWith]
                          exact hc.nonneg _ _
                        have happ : ∀ (L1 L2 : List (Fin (n + 1))) (a : Fin (n + 1)),
                            (List.zipWith c (a :: (L1 ++ L2)) (L1 ++ L2 ++ [0])).sum ≤
                              (List.zipWith c (a :: L1) (L1 ++ [0])).sum +
                                (List.zipWith c (0 :: L2) (L2 ++ [0])).sum := by
                          intro L1 L2
                          induction L1 with
                          | nil => intro a; simpa using htri a 0 L2
                          | cons x L1 ih =>
                            intro a
                            have := ih x
                            simp only [List.cons_append, List.zipWith_cons_cons, List.sum_cons] at this ⊢
                            linarith
                        have hflat : ∀ R' : List (List (Fin (n + 1))),
                            SupplyChainTheory.routeCost c R'.flatten ≤ SupplyChainTheory.solutionCost c R' := by
                          intro R'
                          induction R' with
                          | nil => simp [SupplyChainTheory.routeCost, SupplyChainTheory.closedLength, hc.refl,
                              SupplyChainTheory.solutionCost]
                          | cons L R' ih =>
                            rw [List.flatten_cons]
                            have := happ L R'.flatten 0
                            rw [← hrc, ← hrc, ← hrc] at this
                            simp only [SupplyChainTheory.solutionCost, List.map_cons, List.sum_cons] at ih ⊢
                            linarith
                        have htsp : ∀ U ⊆ clients n, 0 ≤ tspOn c U ∧ tspOn c U ≤ SupplyChainTheory.solutionCost c R := by
                          intro U hU
                          set A := R.flatten.filter (fun v => decide (v ∈ U)) with hA
                          have hAt : IsTourOn U A := by
                            refine ⟨hRn.filter _, fun v => ?_⟩
                            rw [hA, List.mem_filter]
                            constructor
                            · rintro ⟨-, h⟩; simpa using h
                            · intro hv; exact ⟨(hRmem v).2 (hU hv), by simpa using hv⟩
                          have hmem : SupplyChainTheory.routeCost c A ∈
                              {t | ∃ A, IsTourOn U A ∧ t = SupplyChainTheory.routeCost c A} := ⟨A, hAt, rfl⟩
                          have hbdd : BddBelow {t | ∃ A, IsTourOn U A ∧ t = SupplyChainTheory.routeCost c A} := by
                            refine ⟨0, ?_⟩
                            rintro _ ⟨A', -, rfl⟩
                            rw [hrc]; exact hZnn 0 A'
                          constructor
                          · apply le_csInf ⟨_, hmem⟩
                            rintro _ ⟨A', -, rfl⟩
                            rw [hrc]; exact hZnn 0 A'
                          · calc tspOn c U ≤ SupplyChainTheory.routeCost c A := csInf_le hbdd hmem
                              _ ≤ SupplyChainTheory.routeCost c R.flatten := by
                                  rw [hrc, hrc, hA]; exact hfilt _ _ 0
                              _ ≤ _ := hflat R
                        intro U hU
                        obtain ⟨ht0, ht1⟩ := htsp U hU
                        by_cases hα0 : 0 ≤ α
                        · exact le_trans (hctour U hU) (mul_le_mul_of_nonneg_left ht1 hα0)
                        · push_neg at hα0
                          -- degenerate: all distances vanish
                          have hcl := hctour (clients n) le_rfl
                          have hcl0 := (htsp (clients n) le_rfl).1
                          have hZ := hZnn 0 (tour (clients n))
                          rw [← hrc] at hZ
                          have hz : SupplyChainTheory.routeCost c (tour (clients n)) = 0 := by
                            have := mul_nonpos_of_nonpos_of_nonneg hα0.le hcl0
                            linarith
                          have hpre : ∀ (M : List (Fin (n + 1))) (a v : Fin (n + 1)), v ∈ M →
                              c a v ≤ (List.zipWith c (a :: M) (M ++ [0])).sum := by
                            intro M
                            induction M with
                            | nil => intro a v hv; simp at hv
                            | cons x M ih =>
                              intro a v hv
                              simp only [List.cons_append, List.zipWith_cons_cons, List.sum_cons]
                              rcases List.mem_cons.1 hv with rfl | hv
                              · have := hZnn v M; linarith
                              · have := ih x v hv; have := hc.triangle a v x; linarith
                          have h0v : ∀ v, c 0 v = 0 := by
                            intro v
                            by_cases hv0 : v = 0
                            · subst hv0; exact hc.refl 0
                            · have hvc : v ∈ clients n := by simp [clients, hv0]
                              have := hpre _ 0 v (((htour _ le_rfl).2 v).2 hvc)
                              rw [← hrc, hz] at this
                              exact le_antisymm this (hc.nonneg _ _)
                          have hall : ∀ u v, c u v = 0 := by
                            intro u v
                            have h1 := hc.triangle u v 0
                            rw [hc.symm u 0, h0v u, h0v v] at h1
                            exact le_antisymm (by linarith) (hc.nonneg _ _)
                          have hcR : SupplyChainTheory.solutionCost c R = 0 := by
                            rw [show c = fun _ _ => 0 from funext₂ hall]
                            unfold SupplyChainTheory.solutionCost
                            apply List.sum_eq_zero
                            intro x hx
                            obtain ⟨L, -, rfl⟩ := List.mem_map.1 hx
                            simp only [SupplyChainTheory.routeCost, SupplyChainTheory.closedLength]
                            apply List.sum_eq_zero
                            intro y hy
                            obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hy
                            rw [List.getElem_zipWith]
                          have h1 := hctour U hU
                          have h2 : 0 ≤ SupplyChainTheory.routeCost c (tour U) := by
                            rw [hrc]; exact hZnn 0 _
                          have h3 : α * tspOn c U ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hα0.le ht0
                          rw [hcR, mul_zero]; linarith
                      -- coverage: big clients stay uncovered with probability ≤ 1/2
                      have hcov : ∑ S ∈ J.powerset, sampleWeight d δ (Real.log 2) xstar S *
                          ∑ v ∈ uncovered n S, h v ≤ radial c d (clients n) / (1 - δ) := by
                        have hind : ∀ (J' : Finset (List (Fin (n + 1)))) (q : List (Fin (n + 1)) → Prop) [DecidablePred q],
                            (∑ S ∈ J'.powerset, (∏ T ∈ S, p T) * (∏ T ∈ J' \ S, (1 - p T)) *
                              (if ∀ T ∈ S, ¬ q T then (1:ℝ) else 0)) = ∏ T ∈ J'.filter q, (1 - p T) := by
                          intro J' q _
                          induction J' using Finset.induction_on with
                          | empty => simp
                          | insert a J0 ha ih =>
                            rw [Finset.sum_powerset_insert ha]
                            have hnS : ∀ S ∈ J0.powerset, a ∉ S := fun S hS h => ha (Finset.mem_powerset.1 hS h)
                            have hS1 : ∀ S ∈ J0.powerset, insert a J0 \ S = insert a (J0 \ S) := by
                              intro S hS
                              have : a ∉ S := hnS S hS
                              ext x; simp only [Finset.mem_sdiff, Finset.mem_insert]
                              constructor
                              · rintro ⟨h1 | h1, h2⟩
                                · exact Or.inl h1
                                · exact Or.inr ⟨h1, h2⟩
                              · rintro (h1 | ⟨h1, h2⟩)
                                · subst h1; exact ⟨Or.inl rfl, this⟩
                                · exact ⟨Or.inr h1, h2⟩
                            have hS2 : ∀ S ∈ J0.powerset, insert a J0 \ insert a S = J0 \ S := by
                              intro S hS
                              ext x; simp only [Finset.mem_sdiff, Finset.mem_insert]
                              constructor
                              · rintro ⟨h1 | h1, h2⟩
                                · exact absurd (Or.inl h1) h2
                                · exact ⟨h1, fun h => h2 (Or.inr h)⟩
                              · rintro ⟨h1, h2⟩
                                refine ⟨Or.inr h1, ?_⟩
                                rintro (h | h)
                                · exact ha (h ▸ h1)
                                · exact h2 h
                            have e1 : ∀ S ∈ J0.powerset, (∏ T ∈ S, p T) * (∏ T ∈ insert a J0 \ S, (1 - p T)) *
                                (if ∀ T ∈ S, ¬ q T then (1:ℝ) else 0) = (1 - p a) * ((∏ T ∈ S, p T) *
                                (∏ T ∈ J0 \ S, (1 - p T)) * (if ∀ T ∈ S, ¬ q T then (1:ℝ) else 0)) := by
                              intro S hS; rw [hS1 S hS, Finset.prod_insert (fun h => ha (Finset.mem_sdiff.1 h).1)]; ring
                            have e2 : ∀ S ∈ J0.powerset, (∏ T ∈ insert a S, p T) *
                                (∏ T ∈ insert a J0 \ insert a S, (1 - p T)) *
                                (if ∀ T ∈ insert a S, ¬ q T then (1:ℝ) else 0) = (p a * (if q a then 0 else 1)) *
                                ((∏ T ∈ S, p T) * (∏ T ∈ J0 \ S, (1 - p T)) * (if ∀ T ∈ S, ¬ q T then (1:ℝ) else 0)) := by
                              intro S hS
                              rw [hS2 S hS, Finset.prod_insert (hnS S hS)]
                              by_cases hqa : q a
                              · have : ¬ ∀ T ∈ insert a S, ¬ q T := fun h => h a (Finset.mem_insert_self a S) hqa
                                rw [if_neg this, if_pos hqa]; ring
                              · have : (∀ T ∈ insert a S, ¬ q T) ↔ ∀ T ∈ S, ¬ q T := by
                                  rw [Finset.forall_mem_insert]; exact ⟨fun h => h.2, fun h => ⟨hqa, h⟩⟩
                                rw [if_congr this rfl rfl, if_neg hqa]; ring
                            rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, ← Finset.mul_sum, ← Finset.mul_sum, ih]
                            by_cases hqa : q a
                            · rw [Finset.filter_insert, if_pos hqa, if_pos hqa,
                                Finset.prod_insert (fun h => ha (Finset.mem_filter.1 h).1)]; ring
                            · rw [Finset.filter_insert, if_neg hqa, if_neg hqa]; ring
                        have hq : ∀ v, ∑ S ∈ J.powerset, sampleWeight d δ (Real.log 2) xstar S *
                            (if v ∉ covered S then (1:ℝ) else 0) = ∏ T ∈ J.filter (fun T => v ∈ T), (1 - p T) := by
                          intro v
                          refine Eq.trans ?_ (hind J (fun T => v ∈ T))
                          apply Finset.sum_congr rfl; intro S _
                          have : (v ∉ covered S) ↔ ∀ T ∈ S, ¬ v ∈ T := by simp [covered, Finset.mem_biUnion]
                          rw [if_congr this rfl rfl]; rfl
                        have hhalf : ∀ v ∈ bigIn d δ (clients n),
                            ∏ T ∈ J.filter (fun T => v ∈ T), (1 - p T) ≤ 1/2 := by
                          intro v hv
                          have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
                          have hsum : Real.log 2 ≤ ∑ T ∈ J.filter (fun T => v ∈ T), p T := by
                            by_cases hex : ∃ T ∈ J.filter (fun T => v ∈ T), 1 ≤ Real.log 2 * xstar T
                            · obtain ⟨T, hT, h1⟩ := hex
                              have hpT : p T = 1 := min_eq_left h1
                              calc Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
                                _ = p T := hpT.symm
                                _ ≤ _ := Finset.single_le_sum (fun T' hT' => hp0 T' (Finset.mem_filter.1 hT').1) hT
                            · push_neg at hex
                              have : ∀ T ∈ J.filter (fun T => v ∈ T), p T = Real.log 2 * xstar T :=
                                fun T hT => min_eq_right (hex T hT).le
                              rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
                              have := mul_le_mul_of_nonneg_left (hx.1.2 v hv) hl.le
                              linarith only [this]
                          calc ∏ T ∈ J.filter (fun T => v ∈ T), (1 - p T)
                                ≤ ∏ T ∈ J.filter (fun T => v ∈ T), Real.exp (- p T) := by
                                apply Finset.prod_le_prod
                                · intro T _; exact sub_nonneg.2 (hp1 T)
                                · intro T _; have := Real.add_one_le_exp (-p T); linarith only [this]
                            _ = Real.exp (- ∑ T ∈ J.filter (fun T => v ∈ T), p T) := by
                                rw [← Real.exp_sum, Finset.sum_neg_distrib]
                            _ ≤ Real.exp (- Real.log 2) := Real.exp_le_exp.2 (neg_le_neg hsum)
                            _ = 1/2 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
                        have hswap : ∑ S ∈ J.powerset, sampleWeight d δ (Real.log 2) xstar S *
                            ∑ v ∈ uncovered n S, h v = ∑ v ∈ clients n, h v * ∑ S ∈ J.powerset,
                              sampleWeight d δ (Real.log 2) xstar S * (if v ∉ covered S then (1:ℝ) else 0) := by
                          simp_rw [uncovered, Finset.sdiff_eq_filter, Finset.sum_filter, Finset.mul_sum]
                          rw [Finset.sum_comm]
                          apply Finset.sum_congr rfl; intro v _; apply Finset.sum_congr rfl; intro S _
                          split_ifs <;> ring
                        rw [hswap, radial, Finset.sum_div]
                        apply Finset.sum_le_sum
                        intro v hv
                        rw [hq v]
                        have hc0 := hc.nonneg 0 v
                        have hv0 : v ≠ 0 := by simpa [clients] using hv
                        obtain ⟨hdv0, hdv1⟩ := hd v hv0
                        have hL : 0 < 1 - δ := by linarith only [hδ1]
                        have hP0 : 0 ≤ ∏ T ∈ J.filter (fun T => v ∈ T), (1 - p T) :=
                          Finset.prod_nonneg fun T _ => sub_nonneg.2 (hp1 T)
                        by_cases hsm : d v ≤ δ
                        · have hP1 : ∏ T ∈ J.filter (fun T => v ∈ T), (1 - p T) ≤ 1 :=
                            Finset.prod_le_one (fun T _ => sub_nonneg.2 (hp1 T))
                              (fun T hT => by linarith only [hp0 T (Finset.mem_filter.1 hT).1])
                          simp only [hh, if_pos hsm]
                          have : 0 ≤ 2 * d v * c 0 v / (1 - δ) := div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hdv0.le) hc0) hL.le
                          exact mul_le_of_le_one_right this hP1
                        · have hbig : v ∈ bigIn d δ (clients n) := Finset.mem_filter.2 ⟨hv, not_le.mp hsm⟩
                          have := hhalf v hbig
                          simp only [hh, if_neg hsm]
                          rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hL]
                          have h2 : 0 ≤ 2 * c 0 v * (2 * d v - δ) := by
                            apply mul_nonneg (by linarith only [hc0]); linarith only [hsm, hdv0]
                          have h3 := mul_le_mul_of_nonneg_left this h2
                          linarith only [h3, mul_nonneg hδ0.le hc0]
                      have hUS : ∀ S, uncovered n S ⊆ clients n := fun S => Finset.sdiff_subset
                      calc _ ≤ ∑ S ∈ J.powerset, sampleWeight d δ (Real.log 2) xstar S *
                            (α * SupplyChainTheory.solutionCost c R + ∑ v ∈ uncovered n S, h v) := by
                            apply Finset.sum_le_sum
                            intro S hS
                            apply mul_le_mul_of_nonneg_left _ (hw0 S hS)
                            have := hsplitB _ (hUS S)
                            have := hα _ (hUS S)
                            linarith
                        _ = α * SupplyChainTheory.solutionCost c R + ∑ S ∈ J.powerset,
                            sampleWeight d δ (Real.log 2) xstar S * ∑ v ∈ uncovered n S, h v := by
                            simp_rw [mul_add]
                            rw [Finset.sum_add_distrib, ← Finset.sum_mul, hwsum, one_mul]
                        _ ≤ _ := by linarith
                    have hrad' : radial c d (clients n) / (1 - δ) ≤
                        (1 - δ') / (1 - δ) * SupplyChainTheory.solutionCost c R := by
                      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by linarith)]; linarith
                    calc expect d δ (Real.log 2) xstar
                          (fun S => min (alg2Cost c d tour S) (SupplyChainTheory.solutionCost c (B δ')))
                        ≤ ∑ S ∈ J.powerset, sampleWeight d δ (Real.log 2) xstar S * alg2Cost c d tour S := hexpA
                      _ = ∑ S ∈ J.powerset, sampleWeight d δ (Real.log 2) xstar S *
                            ∑ T ∈ S, SupplyChainTheory.routeCost c T +
                          ∑ S ∈ J.powerset, sampleWeight d δ (Real.log 2) xstar S *
                            bestSplit c d (tour (uncovered n S)) := by
                          rw [← Finset.sum_add_distrib]
                          apply Finset.sum_congr rfl; intro S _; rw [alg2Cost, mul_add]
                      _ ≤ (Real.log 2 + α + (1 - δ') / (1 - δ)) * SupplyChainTheory.solutionCost c R := by
                          linarith
                      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hRc
