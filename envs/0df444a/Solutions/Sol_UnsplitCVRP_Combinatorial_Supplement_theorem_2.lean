-- Prove2me | solution 1 for UnsplitCVRP.Combinatorial.Supplement.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:18:47.323862+00:00
-- url     : https://prove2.me/submissions/5620f7a7-4250-44ba-9b89-e4c51eb21684

import Mathlib
import Definitions.Def_SupplyChainTheory_vrp
import Definitions.Def_UnsplitCVRP_Combinatorial_Setting
import Definitions.Def_UnsplitCVRP_Combinatorial_Supplement_ConfigLP

open UnsplitCVRP
open UnsplitCVRP.Combinatorial
open UnsplitCVRP.Combinatorial.Supplement

/-- Theorem 2, p. 2 (proof §4.1, pp. 9–10): every outcome of Algorithm 2 yields a feasible
solution, and its expected cost is at most `(ln 2 + α + 1/(1-δ))` times every feasible
solution's cost. -/
theorem solution {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hc : SupplyChainTheory.VRPMetric c) (d : Fin (n + 1) → ℝ)
    (hd : Demands d) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (α : ℝ)
    (xstar : List (Fin (n + 1)) → ℝ) (hx : IsConfigOptimal c d δ xstar)
    (tour : Finset (Fin (n + 1)) → List (Fin (n + 1)))
    (htour : ∀ U ⊆ clients n, IsTourOn U (tour U))
    (hctour : ∀ U ⊆ clients n, SupplyChainTheory.routeCost c (tour U) ≤ α * tspOn c U) :
    (∀ S ∈ (configTours d δ).powerset, ∃ R, IsSolution d R ∧
      SupplyChainTheory.solutionCost c R ≤ alg2Cost c d tour S) ∧
    ∀ R, IsSolution d R →
      expect d δ (Real.log 2) xstar (alg2Cost c d tour) ≤
        (Real.log 2 + α + 1 / (1 - δ)) * SupplyChainTheory.solutionCost c R := by
          classical
          let path : Fin (n+1) → List (Fin (n+1)) → ℝ :=
            fun a L => (List.zipWith c (a :: L) (L ++ [0])).sum
          have path_nil (a) : path a [] = c a 0 := by simp [path]
          have path_cons (a b) (L) : path a (b :: L) = c a b + path b L := by simp [path]
          have route_path (L) : SupplyChainTheory.routeCost c L = path 0 L := by
            simp [SupplyChainTheory.routeCost, SupplyChainTheory.closedLength, path]
          have path_nonneg (a) (L) : 0 ≤ path a L := by
            induction L generalizing a with
            | nil => simpa [path_nil] using hc.nonneg a 0
            | cons b L ih => rw [path_cons]; exact add_nonneg (hc.nonneg a b) (ih b)
          have route_nonneg (L) : 0 ≤ SupplyChainTheory.routeCost c L := by
            rw [route_path]; exact path_nonneg 0 L
          have sol_nonneg (R) : 0 ≤ SupplyChainTheory.solutionCost c R := by
            exact List.sum_nonneg (by intro x hx; obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hx; exact route_nonneg L)
          have path_triangle (a b) (L) : path a L ≤ c a b + path b L := by
            cases L with
            | nil => simpa [path_nil] using hc.triangle a 0 b
            | cons v L => rw [path_cons, path_cons]; linarith only [hc.triangle a v b]
          have path_sublist (L K : List (Fin (n+1))) (h : L.Sublist K) :
              ∀ a, path a L ≤ path a K := by
            induction h with
            | slnil => intro a; rfl
            | @cons L K v h ih =>
              intro a
              rw [path_cons]
              exact (path_triangle a v L).trans (add_le_add (le_refl _) (ih v))
            | @cons_cons L K v h ih =>
              intro a
              rw [path_cons, path_cons]
              exact add_le_add (le_refl _) (ih v)
          have route_sublist (L K : List (Fin (n+1))) (h : L.Sublist K) :
              SupplyChainTheory.routeCost c L ≤ SupplyChainTheory.routeCost c K := by
            simpa only [route_path] using path_sublist L K h 0
          have load_sublist (L K : List (Fin (n+1))) (h : L.Sublist K)
              (hK : (0 : Fin (n+1)) ∉ K) : load d L ≤ load d K := by
            apply List.Sublist.sum_le_sum (h.map d)
            intro x hx
            obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
            exact (hd v (fun e => hK (e ▸ hv))).1.le
          have split_length (R : List (List (Fin (n+1))))
              (hR : ∀ L ∈ R, L ≠ []) : R.length ≤ R.flatten.length := by
            induction R with
            | nil => simp
            | cons L R ih =>
              have hl : 0 < L.length := List.length_pos_iff.mpr (hR L (by simp))
              have hi := ih (fun K hK => hR K (by simp [hK]))
              simp only [List.length_cons, List.flatten_cons, List.length_append]
              omega
          have split_exists (A : List (Fin (n+1))) (hA : (0 : Fin (n+1)) ∉ A) :
              ∃ R, IsConsecutiveSplit d A R := by
            refine ⟨A.map (fun v => [v]), ?_⟩
            refine ⟨by induction A with | nil => rfl | cons a A ih => simpa using congrArg (List.cons a) (ih (fun hv => hA (by simp [hv]))), ?_⟩
            intro L hL
            obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hL
            exact ⟨by simp, by simpa [load] using (hd v (fun e => hA (e ▸ hv))).2⟩
          have split_attained (A : List (Fin (n+1))) (hAn : A.Nodup)
              (hA0 : (0 : Fin (n+1)) ∉ A) :
              ∃ R, IsConsecutiveSplit d A R ∧
                SupplyChainTheory.solutionCost c R = bestSplit c d A := by
            let C : Set ℝ := {t | ∃ R, IsConsecutiveSplit d A R ∧ t = SupplyChainTheory.solutionCost c R}
            have hCne : C.Nonempty := by
              obtain ⟨R, hR⟩ := split_exists A hA0
              exact ⟨_, R, hR, rfl⟩
            have hf : {R : List (List (Fin (n+1))) | IsConsecutiveSplit d A R}.Finite := by
              let B := {L : List (Fin (n+1)) // L.Nodup}
              have hB : {R : List B | R.length ≤ A.length}.Finite := List.finite_length_le B A.length
              apply (hB.image (fun R => R.map Subtype.val)).subset
              intro R hR
              have hRn : R.flatten.Nodup := hR.1 ▸ hAn
              have hL : ∀ L ∈ R, L.Nodup := (List.nodup_flatten.mp hRn).1
              let R' : List B := R.attach.map (fun L => ⟨L.val, hL L.val L.property⟩)
              refine ⟨R', ?_, ?_⟩
              · simpa [R'] using (hR.1 ▸ split_length R (fun L hL => (hR.2 L hL).1))
              · simp [R']
            have hCf : C.Finite := by
              have he : C = SupplyChainTheory.solutionCost c '' {R | IsConsecutiveSplit d A R} := by
                ext t
                simp only [C, Set.mem_setOf_eq, Set.mem_image]
                constructor
                · rintro ⟨R, hR, rfl⟩; exact ⟨R, hR, rfl⟩
                · rintro ⟨R, hR, rfl⟩; exact ⟨R, hR, rfl⟩
              rw [he]
              exact hf.image _
            obtain ⟨R, hR, he⟩ := hCne.csInf_mem hCf
            exact ⟨R, hR, he.symm⟩
          have prune (Q : List (List (Fin (n+1)))) (U : Finset (Fin (n+1)))
              (hQ : ∀ L ∈ Q, L.Nodup ∧ (0 : Fin (n+1)) ∉ L ∧ load d L ≤ 1)
              (hcover : ∀ v ∈ U, v ∈ Q.flatten) :
              ∃ R, IsSolutionOn d U R ∧ SupplyChainTheory.solutionCost c R ≤ SupplyChainTheory.solutionCost c Q := by
            induction Q generalizing U with
            | nil =>
              refine ⟨[], ?_, le_rfl⟩
              refine ⟨by simp, by simp, ?_⟩
              intro v
              have hv : v ∉ U := by intro hv; simpa using hcover v hv
              simp [hv]
            | cons K Q ih =>
              have hK := hQ K (by simp)
              let L := K.filter (fun v => decide (v ∈ U))
              let V := U \ K.toFinset
              have hLV (v) : v ∈ L ↔ v ∈ K ∧ v ∈ U := by simp [L]
              have hV (v) : v ∈ V ↔ v ∈ U ∧ v ∉ K := by simp [V]
              obtain ⟨R, hR, hcost⟩ := ih V (fun J hJ => hQ J (by simp [hJ])) (by
                intro v hv
                have hv' := (hV v).mp hv
                have hmem := hcover v hv'.1
                simpa [hv'.2] using hmem)
              by_cases hL : L = []
              · have he : V = U := by
                  ext v
                  rw [hV]
                  constructor
                  · exact And.left
                  · intro hv
                    refine ⟨hv, ?_⟩
                    intro hkv
                    have := (hLV v).mpr ⟨hkv, hv⟩
                    simpa [hL] using this
                refine ⟨R, he ▸ hR, ?_⟩
                have hnon := route_nonneg K
                simp only [SupplyChainTheory.solutionCost, List.map_cons, List.sum_cons] at hcost ⊢
                linarith only [hcost, hnon]
              · have hln : L.Nodup := List.Sublist.nodup List.filter_sublist hK.1
                have hl0 : (0 : Fin (n+1)) ∉ L := fun hv => hK.2.1 ((hLV 0).mp hv).1
                have hlcap : load d L ≤ 1 := (load_sublist L K List.filter_sublist hK.2.1).trans hK.2.2
                refine ⟨L :: R, ?_, ?_⟩
                · refine ⟨?_, ?_, ?_⟩
                  · intro J hJ
                    rcases List.mem_cons.mp hJ with rfl | hJ
                    · exact ⟨hL, hl0, hlcap⟩
                    · exact hR.1 J hJ
                  · simp only [List.flatten_cons, List.nodup_append]
                    refine ⟨hln, hR.2.1, ?_⟩
                    intro a ha b hb hab
                    have hb' := (hV b).mp ((hR.2.2 b).mp hb)
                    exact hb'.2 (hab ▸ ((hLV a).mp ha).1)
                  · intro v
                    simp only [List.flatten_cons, List.mem_append, hLV, hR.2.2, hV]
                    tauto
                · have hsub := route_sublist L K List.filter_sublist
                  simp only [SupplyChainTheory.solutionCost, List.map_cons, List.sum_cons] at hcost ⊢
                  linarith only [hcost, hsub]
          have hfeas : ∀ S ∈ (configTours d δ).powerset, ∃ R, IsSolution d R ∧
              SupplyChainTheory.solutionCost c R ≤ alg2Cost c d tour S := by
            intro S hS
            have hS' := Finset.mem_powerset.mp hS
            have hconfig (L) (hL : L ∈ configTours d δ) :
                L.Nodup ∧ L ≠ [] ∧ (∀ v ∈ L, v ∈ bigIn d δ (clients n)) ∧ load d L ≤ 1 := by
              unfold configTours at hL
              obtain ⟨hmem, hdata⟩ := Finset.mem_filter.mp hL
              obtain ⟨K, hK, he⟩ := Finset.mem_map.mp hmem
              exact ⟨he ▸ K.property, hdata⟩
            have hU : uncovered n S ⊆ clients n := Finset.sdiff_subset
            have hA := htour (uncovered n S) hU
            have hA0 : (0 : Fin (n+1)) ∉ tour (uncovered n S) := by
              intro hv
              have := hU ((hA.2 0).mp hv)
              simpa [clients] using this
            obtain ⟨Q, hQ, hcost⟩ := split_attained _ hA.1 hA0
            let P := S.toList ++ Q
            have hP : ∀ L ∈ P, L.Nodup ∧ (0 : Fin (n+1)) ∉ L ∧ load d L ≤ 1 := by
              intro L hL
              rcases List.mem_append.mp hL with hL | hL
              · have hconf := hconfig L (hS' (by simpa using hL))
                refine ⟨hconf.1, ?_, hconf.2.2.2⟩
                intro hzero
                have := (Finset.mem_filter.mp (hconf.2.2.1 0 hzero)).1
                simpa [clients] using this
              · have hN : Q.flatten.Nodup := hQ.1 ▸ hA.1
                refine ⟨(List.nodup_flatten.mp hN).1 L hL, ?_, (hQ.2 L hL).2⟩
                intro hzero
                apply hA0
                rw [← hQ.1]
                exact List.mem_flatten.mpr ⟨L, hL, hzero⟩
            have hcover : ∀ v ∈ clients n, v ∈ P.flatten := by
              intro v hv
              by_cases hvc : v ∈ covered S
              · obtain ⟨L, hL, hvL⟩ := Finset.mem_biUnion.mp hvc
                exact List.mem_flatten.mpr ⟨L, List.mem_append_left _ (by simpa using hL), by simpa using hvL⟩
              · have hvU : v ∈ uncovered n S := Finset.mem_sdiff.mpr ⟨hv, hvc⟩
                have hvA := (hA.2 v).mpr hvU
                rw [← hQ.1] at hvA
                have hflat : Q.flatten ⊆ P.flatten := by simp [P]
                exact hflat hvA
            obtain ⟨R, hR, hRcost⟩ := prune P (clients n) hP hcover
            refine ⟨R, hR, ?_⟩
            calc
              SupplyChainTheory.solutionCost c R ≤ SupplyChainTheory.solutionCost c P := hRcost
              _ = alg2Cost c d tour S := by
                simp only [P, SupplyChainTheory.solutionCost, List.map_append, List.sum_append, alg2Cost]
                change (S.toList.map (SupplyChainTheory.routeCost c)).sum + SupplyChainTheory.solutionCost c Q = _
                rw [hcost]
                congr 1
                exact Finset.sum_map_toList _ _
          have path_to_zero (a) (L : List (Fin (n+1))) : c a 0 ≤ path a L := by
            induction L generalizing a with
            | nil => rw [path_nil]
            | cons b L ih => rw [path_cons]; exact (hc.triangle a 0 b).trans (add_le_add (le_refl _) (ih b))
          have route_visit (L : List (Fin (n+1))) (v) (hv : v ∈ L) :
              2 * c 0 v ≤ SupplyChainTheory.routeCost c L := by
            have h (a) : c a v + c v 0 ≤ path a L := by
              induction L generalizing a with
              | nil => simp at hv
              | cons b L ih =>
                rw [path_cons]
                rcases List.mem_cons.mp hv with rfl | hv
                · exact add_le_add (le_refl _) (path_to_zero v L)
                · have hi := ih hv b
                  linarith only [hi, hc.triangle a v b]
            rw [route_path]
            have hh := h 0
            rw [hc.symm v 0] at hh
            linarith only [hh]
          have route_append (L K : List (Fin (n+1))) :
              SupplyChainTheory.routeCost c (L ++ K) ≤ SupplyChainTheory.routeCost c L + SupplyChainTheory.routeCost c K := by
            have h (a) : path a (L ++ K) ≤ path a L + path 0 K := by
              induction L generalizing a with
              | nil => simpa [path_nil] using path_triangle a 0 K
              | cons b L ih => simp only [List.cons_append, path_cons]; linarith only [ih b]
            simpa only [route_path] using h 0
          have flatten_cost (R : List (List (Fin (n+1)))) :
              SupplyChainTheory.routeCost c R.flatten ≤ SupplyChainTheory.solutionCost c R := by
            induction R with
            | nil => simp [SupplyChainTheory.solutionCost, route_path, path_nil, hc.refl]
            | cons L R ih =>
              simp only [List.flatten_cons, SupplyChainTheory.solutionCost, List.map_cons, List.sum_cons] at ih ⊢
              exact (route_append L R.flatten).trans (add_le_add (le_refl _) ih)
          have tsp_nonneg (U : Finset (Fin (n+1))) : 0 ≤ tspOn c U := by
            apply le_csInf
            · exact ⟨_, U.toList, ⟨Finset.nodup_toList _, by simp⟩, rfl⟩
            · rintro t ⟨A, hA, rfl⟩; exact route_nonneg A
          have tsp_lower (U : Finset (Fin (n+1))) (hU : U ⊆ clients n)
              (R) (hR : IsSolution d R) : tspOn c U ≤ SupplyChainTheory.solutionCost c R := by
            let A := (R.flatten.filter (fun v => decide (v ∈ U))).dedup
            have hA : IsTourOn U A := by
              refine ⟨List.nodup_dedup _, ?_⟩
              intro v
              simp only [A, List.mem_dedup, List.mem_filter, decide_eq_true_eq]
              exact ⟨And.right, fun hv => ⟨(hR.2.2 v).mpr (hU hv), hv⟩⟩
            have hAb : SupplyChainTheory.routeCost c A ≤ SupplyChainTheory.solutionCost c R :=
              (route_sublist A R.flatten ((List.dedup_sublist _).trans List.filter_sublist)).trans (flatten_cost R)
            apply (csInf_le ?_ (show SupplyChainTheory.routeCost c A ∈ {t | ∃ A, IsTourOn U A ∧ t = SupplyChainTheory.routeCost c A} from ⟨A, hA, rfl⟩)).trans hAb
            exact ⟨0, by rintro t ⟨L, hL, rfl⟩; exact route_nonneg L⟩
          have radial_lower (R) (hR : IsSolution d R) : radial c d (clients n) ≤ SupplyChainTheory.solutionCost c R := by
            have hroute (L) (hL : L ∈ R) :
                (L.map (fun v => 2 * d v * c 0 v)).sum ≤ SupplyChainTheory.routeCost c L := by
              have hl := hR.1 L hL
              calc
                _ ≤ (L.map (fun v => d v * SupplyChainTheory.routeCost c L)).sum := by
                  apply List.sum_le_sum
                  intro v hv
                  have hv0 : v ≠ 0 := fun he => hl.2.1 (he ▸ hv)
                  have := mul_le_mul_of_nonneg_left (route_visit L v hv) (hd v hv0).1.le
                  nlinarith only [this]
                _ = load d L * SupplyChainTheory.routeCost c L := by rw [List.sum_map_mul_right]; rfl
                _ ≤ SupplyChainTheory.routeCost c L := by nlinarith only [route_nonneg L, hl.2.2]
            have he : R.flatten.toFinset = clients n := by ext v; simpa using hR.2.2 v
            rw [radial, ← he, List.sum_toFinset _ hR.2.1]
            have hsum (Q : List (List (Fin (n+1)))) :
                (Q.flatten.map (fun v => 2 * d v * c 0 v)).sum =
                (Q.map (fun L => (L.map (fun v => 2 * d v * c 0 v)).sum)).sum := by
              induction Q with
              | nil => simp
              | cons L Q ih => simp [List.map_append, ih, Function.comp_def]
            rw [hsum]
            exact List.sum_le_sum hroute
          have lp_lower (R) (hR : IsSolution d R) : configCost c d δ xstar ≤ SupplyChainTheory.solutionCost c R := by
            let F : List (Fin (n+1)) → List (Fin (n+1)) := fun L => L.filter (fun v => decide (δ < d v))
            have hF (L) (hL : L ∈ R) (hne : F L ≠ []) : F L ∈ configTours d δ := by
              apply Finset.mem_filter.mpr
              have hLn := (List.nodup_flatten.mp hR.2.1).1 L hL
              refine ⟨Finset.mem_map.mpr ⟨⟨F L, List.Sublist.nodup List.filter_sublist hLn⟩, Finset.mem_univ _, rfl⟩, hne, ?_, ?_⟩
              · intro v hv
                obtain ⟨hvL, hvd⟩ := List.mem_filter.mp hv
                apply Finset.mem_filter.mpr
                exact ⟨(hR.2.2 v).mp (List.mem_flatten.mpr ⟨L, hL, hvL⟩), of_decide_eq_true hvd⟩
              · exact (load_sublist _ L List.filter_sublist (hR.1 L hL).2.1).trans (hR.1 L hL).2.2
            let y : List (Fin (n+1)) → ℝ := fun T =>
              (R.map (fun L => if F L ≠ [] ∧ F L = T then (1 : ℝ) else 0)).sum
            have hyn (T) : 0 ≤ y T := by
              apply List.sum_nonneg
              intro x hx
              obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hx
              split_ifs <;> norm_num
            have hy : IsConfigFeasible d δ y := by
              refine ⟨fun T hT => hyn T, ?_⟩
              intro v hv
              obtain ⟨L, hL, hvL⟩ := List.mem_flatten.mp ((hR.2.2 v).mpr (Finset.mem_filter.mp hv).1)
              have hvF : v ∈ F L := by simp [F, hvL, (Finset.mem_filter.mp hv).2]
              have hne : F L ≠ [] := by intro he; simpa [he] using hvF
              have hcfg := hF L hL hne
              have hyone : 1 ≤ y (F L) := by
                have hone : (1 : ℝ) ∈ R.map (fun K => if F K ≠ [] ∧ F K = F L then (1 : ℝ) else 0) := by
                  exact List.mem_map.mpr ⟨L, hL, by simp [hne]⟩
                apply List.single_le_sum _ 1 hone
                intro x hx
                obtain ⟨K, hK, rfl⟩ := List.mem_map.mp hx
                split_ifs <;> norm_num
              apply hyone.trans
              exact Finset.single_le_sum (fun T hT => hyn T) (Finset.mem_filter.mpr ⟨hcfg, hvF⟩)
            apply (hx.2 y hy).trans
            have hlin (Q : List (List (Fin (n+1)))) (hQ : ∀ L ∈ Q, F L ≠ [] → F L ∈ configTours d δ) :
                (∑ T ∈ configTours d δ, SupplyChainTheory.routeCost c T *
                  (Q.map (fun L => if F L ≠ [] ∧ F L = T then (1 : ℝ) else 0)).sum) =
                (Q.map (fun L => if F L = [] then (0 : ℝ) else SupplyChainTheory.routeCost c (F L))).sum := by
              induction Q with
              | nil => simp
              | cons L Q ih =>
                simp only [List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib]
                rw [ih (fun K hK => hQ K (by simp [hK]))]
                congr 1
                by_cases he : F L = []
                · simp [he]
                · have hcF := hQ L (by simp) he
                  simp [he, eq_comm, hcF]
            change (∑ T ∈ configTours d δ, SupplyChainTheory.routeCost c T * y T) ≤ _
            change (∑ T ∈ configTours d δ, SupplyChainTheory.routeCost c T *
              (R.map (fun L => if F L ≠ [] ∧ F L = T then (1 : ℝ) else 0)).sum) ≤ _
            rw [hlin R hF]
            apply List.sum_le_sum
            intro L hL
            split_ifs
            · exact route_nonneg L
            · exact route_sublist _ L List.filter_sublist
          have cut_before (B : List (Fin (n+1))) (v) (K : List (Fin (n+1))) :
              SupplyChainTheory.routeCost c B + SupplyChainTheory.routeCost c (v :: K) ≤
                SupplyChainTheory.routeCost c (B ++ v :: K) + 2 * c 0 v := by
            have hh (a) : path a B + path 0 (v :: K) ≤ path a (B ++ v :: K) + 2 * c 0 v := by
              induction B generalizing a with
              | nil => simp only [path_nil, List.nil_append, path_cons]; linarith only [hc.triangle a 0 v, hc.symm v 0]
              | cons b B ih => simp only [path_cons, List.cons_append]; have hi := ih b; rw [path_cons] at hi; linarith only [hi]
            simpa only [route_path] using hh 0
          have cut_after (B : List (Fin (n+1))) (v) (K : List (Fin (n+1))) :
              SupplyChainTheory.routeCost c (B ++ [v]) + SupplyChainTheory.routeCost c K ≤
                SupplyChainTheory.routeCost c (B ++ v :: K) + 2 * c 0 v := by
            have hh (a) : path a (B ++ [v]) + path 0 K ≤ path a (B ++ v :: K) + 2 * c 0 v := by
              induction B generalizing a with
              | nil => simp only [List.nil_append, path_cons, path_nil]; rw [hc.symm v 0]; linarith only [path_triangle 0 v K]
              | cons b B ih => simp only [List.cons_append, path_cons]; linarith only [ih b]
            simpa only [route_path] using hh 0
          have split_bound (A : List (Fin (n+1))) (hAn : A.Nodup) (hA0 : (0 : Fin (n+1)) ∉ A) :
              bestSplit c d A ≤ SupplyChainTheory.routeCost c A +
                ∑ v ∈ A.toFinset, (if δ < d v then 4 else 2) * c 0 v * d v / (1 - δ) := by
            let t : ℝ := 1 - δ
            have ht : 0 < t := sub_pos.mpr hδ1
            let charge : Fin (n+1) → ℝ := fun v => (if δ < d v then 4 else 2) * c 0 v
            have hcharge (v) : 0 ≤ charge v := by exact mul_nonneg (by split_ifs <;> norm_num) (hc.nonneg 0 v)
            have hmin (Q) (hQ : IsConsecutiveSplit d A Q) : bestSplit c d A ≤ SupplyChainTheory.solutionCost c Q := by
              apply csInf_le
              · exact ⟨0, by rintro z ⟨R, hR, rfl⟩; exact sol_nonneg R⟩
              · exact ⟨Q, hQ, rfl⟩
            have hdiscrete (N : ℕ) (hN : 0 < N) :
                (N : ℝ) * bestSplit c d A ≤ (N : ℝ) * SupplyChainTheory.routeCost c A +
                  (N : ℝ) * (A.map (fun v => charge v * d v / t)).sum + (A.map charge).sum := by
              have hNr : (0 : ℝ) < N := by exact_mod_cast hN
              let k : Fin (n+1) → ℕ := fun v => ⌈(N : ℝ) * d v / t⌉₊
              let units (L : List (Fin (n+1))) : ℕ := (L.map k).sum
              let β : ℝ := t / N
              have hβ : 0 ≤ β := (div_pos ht hNr).le
              have hklo (v) : d v ≤ β * (k v : ℝ) := by
                have hh := (div_le_iff₀ ht).mp (Nat.le_ceil ((N : ℝ) * d v / t))
                calc
                  d v ≤ t * (k v : ℝ) / (N : ℝ) := (le_div_iff₀ hNr).2 (by change (N : ℝ) * d v ≤ (k v : ℝ) * t at hh; nlinarith only [hh])
                  _ = β * (k v : ℝ) := by dsimp [β]; ring
              have hload (L : List (Fin (n+1))) : load d L ≤ β * (units L : ℝ) := by
                induction L with
                | nil => simp [load, units]
                | cons v L ih =>
                  simp only [load, List.map_cons, List.sum_cons] at ih ⊢
                  have hu : units (v :: L) = k v + units L := rfl
                  rw [hu, Nat.cast_add]
                  nlinarith only [ih, hklo v]
              have hcap (L : List (Fin (n+1))) (hL : units L ≤ N) : load d L ≤ t := by
                have hh := mul_le_mul_of_nonneg_left (show (units L : ℝ) ≤ N by exact_mod_cast hL) hβ
                have he : β * (N : ℝ) = t := by dsimp [β]; field_simp
                rw [he] at hh
                exact (hload L).trans hh
              let bad (q θ z : ℕ) : Prop := (q + θ) / N < (q + θ + z) / N
              let pen (q θ : ℕ) (L : List (Fin (n+1))) : ℝ :=
                (L.foldr (fun v (f : ℕ → ℝ) q => (if bad q θ (k v) then charge v else 0) + f (q + k v)) (fun _ => 0)) q
              have pen_nil (q θ) : pen q θ [] = 0 := rfl
              have pen_cons (q θ v L) : pen q θ (v :: L) =
                  (if bad q θ (k v) then charge v else 0) + pen (q + k v) θ L := rfl
              have hbuild (L : List (Fin (n+1))) : ∀ (B : List (Fin (n+1))) (q θ : ℕ),
                  (0 : Fin (n+1)) ∉ B ++ L → units B ≤ (q + θ) % N →
                  ∃ Q, IsConsecutiveSplit d (B ++ L) Q ∧
                    SupplyChainTheory.solutionCost c Q ≤ SupplyChainTheory.routeCost c (B ++ L) + pen q θ L := by
                induction L with
                | nil =>
                  intro B q θ h0 hu
                  have hb := hcap B (hu.trans (Nat.mod_lt _ hN).le)
                  by_cases hB : B = []
                  · subst B
                    refine ⟨[], ⟨rfl, by simp⟩, ?_⟩
                    simp [SupplyChainTheory.solutionCost, pen_nil, pen_cons, route_path, path_nil, hc.refl]
                  · refine ⟨[B], ⟨by simp, ?_⟩, ?_⟩
                    · intro K hK; have he : K = B := by simpa using hK
                      subst K; exact ⟨hB, by dsimp [t] at hb; linarith only [hb, hδ0]⟩
                    · simp [SupplyChainTheory.solutionCost, pen]
                | cons v L ih =>
                  intro B q θ h0 hu
                  have hv0 : v ≠ 0 := by intro he; apply h0; simp [he]
                  have hv1 := (hd v hv0).2
                  have htail0 : (0 : Fin (n+1)) ∉ L := by intro hh; apply h0; simp [hh]
                  have hBcap := hcap B (hu.trans (Nat.mod_lt _ hN).le)
                  by_cases hb : bad q θ (k v)
                  · obtain ⟨Q, hQ, hcQ⟩ := ih [] (q + k v) θ (by simpa using htail0) (by simp [units])
                    by_cases hvbig : δ < d v
                    · have hcut1 := cut_before B v ([] : List (Fin (n+1)))
                      have hcut2 := cut_after B v L
                      by_cases hB : B = []
                      · subst B
                        refine ⟨[v] :: Q, ⟨?_, ?_⟩, ?_⟩
                        · simpa using congrArg (List.cons v) hQ.1
                        · intro K hK
                          rcases List.mem_cons.mp hK with rfl | hK
                          · exact ⟨by simp, by simpa [load] using hv1⟩
                          · exact hQ.2 K hK
                        · simp only [SupplyChainTheory.solutionCost, List.map_cons, List.sum_cons] at hcQ ⊢
                          simp only [pen_nil, pen_cons, if_pos hb, charge, if_pos hvbig]
                          simpa only [List.nil_append, add_assoc] using (show SupplyChainTheory.routeCost c [v] + (Q.map (SupplyChainTheory.routeCost c)).sum ≤ SupplyChainTheory.routeCost c (v :: L) + 4 * c 0 v + pen (q + k v) θ L by
                            have hh := cut_after [] v L
                            simp only [List.nil_append] at hh hcQ
                            linarith only [hcQ, hh, hc.nonneg 0 v])
                      · refine ⟨B :: [v] :: Q, ⟨?_, ?_⟩, ?_⟩
                        · simpa using congrArg (fun K => B ++ v :: K) hQ.1
                        · intro K hK
                          rcases List.mem_cons.mp hK with rfl | hK
                          · exact ⟨hB, by dsimp [t] at hBcap; linarith only [hBcap, hδ0]⟩
                          · rcases List.mem_cons.mp hK with rfl | hK
                            · exact ⟨by simp, by simpa [load] using hv1⟩
                            · exact hQ.2 K hK
                        · simp only [SupplyChainTheory.solutionCost, List.map_cons, List.sum_cons] at hcQ ⊢
                          simp only [pen_nil, pen_cons, if_pos hb, charge, if_pos hvbig]
                          simp only [List.nil_append, List.append_nil] at hcQ hcut1
                          linarith only [hcQ, hcut1, hcut2]
                    · have hsmall : d v ≤ δ := le_of_not_gt hvbig
                      have hbvcap : load d (B ++ [v]) ≤ 1 := by
                        simp only [load, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
                        change load d B + d v ≤ 1
                        dsimp [t] at hBcap
                        linarith only [hBcap, hsmall]
                      refine ⟨(B ++ [v]) :: Q, ⟨?_, ?_⟩, ?_⟩
                      · simpa [List.append_assoc] using congrArg (fun K => (B ++ [v]) ++ K) hQ.1
                      · intro K hK
                        rcases List.mem_cons.mp hK with rfl | hK
                        · exact ⟨by simp, hbvcap⟩
                        · exact hQ.2 K hK
                      · have hh := cut_after B v L
                        simp only [SupplyChainTheory.solutionCost, List.map_cons, List.sum_cons] at hcQ ⊢
                        simp only [pen_nil, pen_cons, if_pos hb, charge, if_neg hvbig]
                        simp only [List.nil_append] at hcQ
                        linarith only [hcQ, hh]
                  · have hquot : (q + θ + k v) / N = (q + θ) / N := by
                      apply le_antisymm (Nat.le_of_not_gt hb)
                      exact Nat.div_le_div_right (by omega)
                    have hmod : (q + k v + θ) % N = (q + θ) % N + k v := by
                      have h1 := Nat.mod_add_div (q + θ) N
                      have h2 := Nat.mod_add_div (q + θ + k v) N
                      rw [hquot] at h2
                      have he : q + θ + k v = q + k v + θ := by omega
                      rw [he] at h2
                      omega
                    have hunew : units (B ++ [v]) ≤ (q + k v + θ) % N := by
                      rw [hmod]
                      simpa [units, List.map_append] using Nat.add_le_add_right hu (k v)
                    obtain ⟨Q, hQ, hcQ⟩ := ih (B ++ [v]) (q + k v) θ (by simpa [List.append_assoc] using h0) hunew
                    refine ⟨Q, ?_, ?_⟩
                    · simpa [List.append_assoc] using hQ
                    · simpa [pen_nil, pen_cons, hb, List.append_assoc] using hcQ
              have hcard (q z : ℕ) : ((Finset.range N).filter (fun θ => bad q θ z)).card ≤ z := by
                have hh : ((Finset.range N).filter (fun θ => bad q θ z)).card ≤ (Finset.range z).card := by
                  apply Finset.card_le_card_of_injOn (fun θ => (q + θ + z) % N)
                  · intro θ hθ
                    have hθ' := Finset.mem_filter.mp hθ
                    have hb := hθ'.2
                    change (q + θ) / N < (q + θ + z) / N at hb
                    have h1 := Nat.mod_add_div (q + θ) N
                    have h2 := Nat.mod_add_div (q + θ + z) N
                    have hm := Nat.mod_lt (q + θ) hN
                    have hmul := Nat.mul_le_mul_left N (Nat.succ_le_of_lt hb)
                    simp only [Nat.mul_succ] at hmul
                    apply Finset.mem_range.mpr
                    change (q + θ + z) % N < z
                    omega
                  · intro θ hθ φ hφ he
                    have hθN := (Finset.mem_range.mp (Finset.mem_filter.mp hθ).1)
                    have hφN := (Finset.mem_range.mp (Finset.mem_filter.mp hφ).1)
                    have hmod : θ ≡ φ [MOD N] := by
                      apply Nat.ModEq.add_left_cancel (Nat.ModEq.refl q)
                      apply Nat.ModEq.add_right_cancel (Nat.ModEq.refl z)
                      exact he
                    simpa [Nat.ModEq, Nat.mod_eq_of_lt hθN, Nat.mod_eq_of_lt hφN] using hmod
                simpa using hh
              have hpens (L : List (Fin (n+1))) : ∀ q,
                  (∑ θ ∈ Finset.range N, pen q θ L) ≤ (L.map (fun v => charge v * (k v : ℝ))).sum := by
                induction L with
                | nil => intro q; simp [pen_nil, pen_cons]
                | cons v L ih =>
                  intro q
                  simp only [pen_nil, pen_cons, Finset.sum_add_distrib, List.map_cons, List.sum_cons]
                  apply add_le_add _ (ih (q + k v))
                  rw [← Finset.sum_filter]
                  simp only [Finset.sum_const, nsmul_eq_mul]
                  have hh : (((Finset.range N).filter (fun θ => bad q θ (k v))).card : ℝ) ≤ k v := by exact_mod_cast hcard q (k v)
                  nlinarith only [hh, hcharge v]
              have hpoint (θ) (hθ : θ ∈ Finset.range N) : bestSplit c d A ≤ SupplyChainTheory.routeCost c A + pen 0 θ A := by
                obtain ⟨Q, hQ, hcQ⟩ := hbuild A [] 0 θ (by simpa using hA0) (by simp [units])
                exact (hmin Q (by simpa using hQ)).trans (by simpa using hcQ)
              have hsum := Finset.sum_le_sum hpoint
              simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
              have hsum' := hpens A 0
              have hround : (A.map (fun v => charge v * (k v : ℝ))).sum ≤
                  (N : ℝ) * (A.map (fun v => charge v * d v / t)).sum + (A.map charge).sum := by
                have he : (N : ℝ) * (A.map (fun v => charge v * d v / t)).sum + (A.map charge).sum =
                    (A.map (fun v => (N : ℝ) * (charge v * d v / t) + charge v)).sum := by
                  rw [List.sum_map_add, List.sum_map_mul_left]
                rw [he]
                apply List.sum_le_sum
                intro v hv
                have hv0 : v ≠ 0 := by intro he; exact hA0 (he ▸ hv)
                have hdv := (hd v hv0).1.le
                have hk := (Nat.ceil_lt_add_one (show 0 ≤ (N : ℝ) * d v / t by positivity)).le
                have hm := mul_le_mul_of_nonneg_left hk (hcharge v)
                calc
                  charge v * (k v : ℝ) ≤ charge v * ((N : ℝ) * d v / t + 1) := hm
                  _ = (N : ℝ) * (charge v * d v / t) + charge v := by ring
              linarith only [hsum, hsum', hround]
            have heq : (A.map (fun v => charge v * d v / t)).sum =
                ∑ v ∈ A.toFinset, (if δ < d v then 4 else 2) * c 0 v * d v / (1 - δ) := by
              rw [List.sum_toFinset _ hAn]
            rw [← heq]
            apply le_of_forall_pos_le_add
            intro ε hε
            have hC : 0 ≤ (A.map charge).sum := by
              apply List.sum_nonneg
              intro z hz
              obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hz
              exact hcharge v
            obtain ⟨N, hN⟩ := exists_nat_gt ((A.map charge).sum / ε)
            have hNr : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
            have hNnat : 0 < N := by exact_mod_cast hNr
            have hh := hdiscrete N hNnat
            have hsmall := (div_lt_iff₀ hε).mp hN
            nlinarith only [hh, hsmall, hNr]
          let J := configTours d δ
          let γ : ℝ := Real.log 2
          let p := roundProb γ xstar
          let w := sampleWeight d δ γ xstar
          have hγ : 0 ≤ γ := Real.log_nonneg (by norm_num)
          have hp (T) (hT : T ∈ J) : 0 ≤ p T ∧ p T ≤ 1 := by
            exact ⟨le_min (by norm_num) (mul_nonneg hγ (hx.1.1 T hT)), min_le_left _ _⟩
          have hw (S : Finset (List (Fin (n+1)))) (hS : S ⊆ J) : 0 ≤ w S := by
            apply mul_nonneg
            · exact Finset.prod_nonneg (fun T hT => (hp T (hS hT)).1)
            · exact Finset.prod_nonneg (fun T hT => sub_nonneg.mpr (hp T (Finset.mem_sdiff.mp hT).1).2)
          have generating (f : List (Fin (n+1)) → ℝ) :
              (∑ S ∈ J.powerset, w S * ∏ T ∈ S, f T) =
                ∏ T ∈ J, (1 - p T + p T * f T) := by
            calc
              _ = ∑ S ∈ J.powerset, (∏ T ∈ S, p T * f T) * ∏ T ∈ J \ S, (1 - p T) := by
                apply Finset.sum_congr rfl
                intro S hS
                rw [Finset.prod_mul_distrib]
                change ((∏ T ∈ S, p T) * ∏ T ∈ J \ S, (1 - p T)) * (∏ T ∈ S, f T) = _
                ring
              _ = ∏ T ∈ J, (p T * f T + (1 - p T)) := (Finset.prod_add _ _ _).symm
              _ = _ := by apply Finset.prod_congr rfl; intro T hT; ring
          have weight_sum : ∑ S ∈ J.powerset, w S = 1 := by
            have hg := generating (fun _ => 1)
            simpa using hg
          have avoid (v : Fin (n+1)) : probNotCovered d δ γ xstar v =
              ∏ T ∈ J.filter (fun T => v ∈ T), (1 - p T) := by
            have hi (S : Finset (List (Fin (n+1)))) :
                (∏ T ∈ S, if v ∉ T then (1 : ℝ) else 0) = if v ∉ covered S then 1 else 0 := by
              rw [Finset.prod_ite_zero]
              simp only [Finset.prod_const_one]
              have he : (∀ T ∈ S, v ∉ T) ↔ v ∉ covered S := by simp [covered]
              simp only [he]
            have hg := generating (fun T => if v ∉ T then 1 else 0)
            simp_rw [hi] at hg
            have hprod : (∏ T ∈ J, (1 - p T + p T * (if v ∉ T then 1 else 0))) =
                ∏ T ∈ J.filter (fun T => v ∈ T), (1 - p T) := by
              rw [Finset.prod_filter]
              apply Finset.prod_congr rfl
              intro T hT
              by_cases hv : v ∈ T <;> simp [hv]
            rw [hprod] at hg
            rw [← hg]
            unfold probNotCovered
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro S hS
            by_cases hs : v ∉ covered S
            · simp only [if_pos hs, mul_one]
              rfl
            · simp only [if_neg hs, mul_zero]
          have uncovered_half (v : Fin (n+1)) (hv : v ∈ bigIn d δ (clients n)) :
              probNotCovered d δ γ xstar v ≤ (1/2 : ℝ) := by
            rw [avoid]
            calc
              _ ≤ ∏ T ∈ J.filter (fun T => v ∈ T), Real.exp (-γ * xstar T) := by
                apply Finset.prod_le_prod
                · intro T hT; exact sub_nonneg.mpr (hp T (Finset.mem_filter.mp hT).1).2
                · intro T hT
                  by_cases he : γ * xstar T ≤ 1
                  · have hpT : p T = γ * xstar T := min_eq_right he
                    rw [hpT]
                    simpa only [neg_mul] using Real.one_sub_le_exp_neg (γ * xstar T)
                  · have hpT : p T = 1 := min_eq_left (le_of_not_ge he)
                    rw [hpT, sub_self]
                    exact (Real.exp_pos _).le
              _ = Real.exp (-γ * ∑ T ∈ J.filter (fun T => v ∈ T), xstar T) := by
                rw [Finset.mul_sum, Real.exp_sum]
              _ ≤ Real.exp (-γ) := by
                apply Real.exp_le_exp.mpr
                have hh := hx.1.2 v hv
                change 1 ≤ ∑ T ∈ J.filter (fun T => v ∈ T), xstar T at hh
                nlinarith only [hh, hγ]
              _ = (1/2 : ℝ) := by
                rw [show γ = Real.log 2 from rfl, Real.exp_neg, Real.exp_log (by norm_num)]
                norm_num
          have marginal (T) (hT : T ∈ J) :
              (∑ S ∈ J.powerset, if T ∈ S then w S else 0) = p T := by
            have hi (S : Finset (List (Fin (n+1)))) :
                (∏ K ∈ S, if K ≠ T then (1 : ℝ) else 0) = if T ∉ S then 1 else 0 := by
              rw [Finset.prod_ite_zero]
              simp only [Finset.prod_const_one]
              have he : (∀ K ∈ S, K ≠ T) ↔ T ∉ S := by simp [eq_comm]
              simp only [he]
            have hg := generating (fun K => if K ≠ T then 1 else 0)
            simp_rw [hi] at hg
            have hprod : (∏ K ∈ J, (1 - p K + p K * (if K ≠ T then 1 else 0))) = 1 - p T := by
              rw [Finset.prod_eq_single T]
              · simp
              · intro K hK hKT; simp [hKT]
              · intro hn; exact (hn hT).elim
            rw [hprod] at hg
            have he : (∑ S ∈ J.powerset, if T ∈ S then w S else 0) +
                (∑ S ∈ J.powerset, w S * if T ∉ S then 1 else 0) = 1 := by
              calc
                _ = ∑ S ∈ J.powerset, w S := by
                  rw [← Finset.sum_add_distrib]
                  apply Finset.sum_congr rfl
                  intro S hS
                  by_cases hm : T ∈ S <;> simp [hm]
                _ = 1 := weight_sum
            linarith only [he, hg]
          have sampled_cost : expect d δ γ xstar (fun S => ∑ T ∈ S, SupplyChainTheory.routeCost c T) ≤
              γ * configCost c d δ xstar := by
            have he (f : List (Fin (n+1)) → ℝ) :
                (∑ S ∈ J.powerset, w S * ∑ T ∈ S, f T) = ∑ T ∈ J, p T * f T := by
              calc
                _ = ∑ S ∈ J.powerset, ∑ T ∈ J, if T ∈ S then w S * f T else 0 := by
                  apply Finset.sum_congr rfl
                  intro S hS
                  rw [Finset.mul_sum, ← Finset.sum_filter]
                  have hh : J.filter (fun T => T ∈ S) = S := by
                    ext T; simp only [Finset.mem_filter]; exact ⟨And.right, fun h => ⟨Finset.mem_powerset.mp hS h, h⟩⟩
                  rw [hh]
                _ = ∑ T ∈ J, ∑ S ∈ J.powerset, if T ∈ S then w S * f T else 0 := Finset.sum_comm
                _ = ∑ T ∈ J, p T * f T := by
                  apply Finset.sum_congr rfl
                  intro T hT
                  rw [← marginal T hT, Finset.sum_mul]
                  apply Finset.sum_congr rfl
                  intro S hS
                  split_ifs <;> simp
            change (∑ S ∈ J.powerset, w S * ∑ T ∈ S, SupplyChainTheory.routeCost c T) ≤ _
            rw [he]
            unfold configCost
            rw [Finset.mul_sum]
            apply Finset.sum_le_sum
            intro T hT
            have hpT : p T ≤ γ * xstar T := min_le_right _ _
            nlinarith only [mul_le_mul_of_nonneg_right hpT (route_nonneg T)]
          have avoid_le_one (v : Fin (n+1)) : probNotCovered d δ γ xstar v ≤ 1 := by
            calc
              _ ≤ ∑ S ∈ J.powerset, w S := by
                change (∑ S ∈ J.powerset.filter (fun S => v ∉ covered S), w S) ≤ _
                rw [Finset.sum_filter]
                apply Finset.sum_le_sum
                intro S hS
                by_cases hv : v ∉ covered S
                · simp only [if_pos hv]
                  exact le_rfl
                · simp only [if_neg hv]
                  exact hw S (Finset.mem_powerset.mp hS)
              _ = 1 := weight_sum
          have repair_expect (R) (hR : IsSolution d R) (hα : 0 ≤ α) :
              expect d δ γ xstar (fun S => bestSplit c d (tour (uncovered n S))) ≤
                α * SupplyChainTheory.solutionCost c R + radial c d (clients n) / (1 - δ) := by
            let fee : Fin (n+1) → ℝ := fun v => (if δ < d v then 4 else 2) * c 0 v * d v / (1 - δ)
            have ht : 0 < 1 - δ := sub_pos.mpr hδ1
            have hfee (v) (hv : v ∈ clients n) : 0 ≤ fee v := by
              have hv0 : v ≠ 0 := (Finset.mem_erase.mp hv).1
              have hdn := (hd v hv0).1.le
              have hcn := hc.nonneg 0 v
              exact div_nonneg
                (mul_nonneg (mul_nonneg (by split_ifs <;> norm_num) hcn) hdn) ht.le
            have hpoint (S : Finset (List (Fin (n+1)))) :
                bestSplit c d (tour (uncovered n S)) ≤
                  α * SupplyChainTheory.solutionCost c R + ∑ v ∈ uncovered n S, fee v := by
              have hU : uncovered n S ⊆ clients n := Finset.sdiff_subset
              have hA := htour _ hU
              have hA0 : (0 : Fin (n+1)) ∉ tour (uncovered n S) := by
                intro hv
                have := hU ((hA.2 0).mp hv)
                simpa [clients] using this
              have he : (tour (uncovered n S)).toFinset = uncovered n S := by
                ext v; simpa using hA.2 v
              have hb := split_bound _ hA.1 hA0
              rw [he] at hb
              have hh := (hctour _ hU).trans (mul_le_mul_of_nonneg_left (tsp_lower _ hU R hR) hα)
              exact hb.trans (add_le_add hh le_rfl)
            have hfubini : (∑ S ∈ J.powerset, w S * ∑ v ∈ uncovered n S, fee v) =
                ∑ v ∈ clients n, fee v * probNotCovered d δ γ xstar v := by
              calc
                _ = ∑ S ∈ J.powerset, ∑ v ∈ clients n, if v ∉ covered S then w S * fee v else 0 := by
                  apply Finset.sum_congr rfl
                  intro S hS
                  have he : uncovered n S = (clients n).filter (fun v => v ∉ covered S) := by ext v; simp [uncovered]
                  rw [he, Finset.sum_filter, Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro v hv
                  split_ifs <;> simp
                _ = ∑ v ∈ clients n, ∑ S ∈ J.powerset, if v ∉ covered S then w S * fee v else 0 := Finset.sum_comm
                _ = _ := by
                  apply Finset.sum_congr rfl
                  intro v hv
                  unfold probNotCovered
                  rw [Finset.sum_filter, Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro S hS
                  split_ifs <;> simp [w, mul_comm]
            have hfees : (∑ v ∈ clients n, fee v * probNotCovered d δ γ xstar v) ≤
                radial c d (clients n) / (1 - δ) := by
              rw [radial, Finset.sum_div]
              apply Finset.sum_le_sum
              intro v hv
              by_cases hb : δ < d v
              · calc
                  _ ≤ fee v * (1/2) := mul_le_mul_of_nonneg_left (uncovered_half v (Finset.mem_filter.mpr ⟨hv, hb⟩)) (hfee v hv)
                  _ = 2 * d v * c 0 v / (1 - δ) := by dsimp [fee]; rw [if_pos hb]; ring
              · calc
                  _ ≤ fee v * 1 := mul_le_mul_of_nonneg_left (avoid_le_one v) (hfee v hv)
                  _ = 2 * d v * c 0 v / (1 - δ) := by dsimp [fee]; rw [if_neg hb]; ring
            change (∑ S ∈ J.powerset, w S * bestSplit c d (tour (uncovered n S))) ≤ _
            calc
              _ ≤ ∑ S ∈ J.powerset, w S * (α * SupplyChainTheory.solutionCost c R + ∑ v ∈ uncovered n S, fee v) := by
                apply Finset.sum_le_sum
                intro S hS
                exact mul_le_mul_of_nonneg_left (hpoint S) (hw S (Finset.mem_powerset.mp hS))
              _ = α * SupplyChainTheory.solutionCost c R + ∑ v ∈ clients n, fee v * probNotCovered d δ γ xstar v := by
                simp only [mul_add, Finset.sum_add_distrib]
                rw [hfubini, ← Finset.sum_mul, weight_sum, one_mul]
              _ ≤ _ := add_le_add le_rfl hfees
          refine ⟨hfeas, ?_⟩
          by_cases hα : 0 ≤ α
          · intro R hR
            have ht : 0 ≤ 1 - δ := (sub_pos.mpr hδ1).le
            have he : expect d δ γ xstar (alg2Cost c d tour) =
                expect d δ γ xstar (fun S => ∑ T ∈ S, SupplyChainTheory.routeCost c T) +
                expect d δ γ xstar (fun S => bestSplit c d (tour (uncovered n S))) := by
              simp only [expect, alg2Cost, mul_add, Finset.sum_add_distrib]
            change expect d δ γ xstar (alg2Cost c d tour) ≤ _
            rw [he]
            calc
              _ ≤ γ * configCost c d δ xstar + (α * SupplyChainTheory.solutionCost c R + radial c d (clients n) / (1 - δ)) :=
                add_le_add sampled_cost (repair_expect R hR hα)
              _ ≤ γ * SupplyChainTheory.solutionCost c R + (α * SupplyChainTheory.solutionCost c R + SupplyChainTheory.solutionCost c R / (1 - δ)) := by
                exact add_le_add (mul_le_mul_of_nonneg_left (lp_lower R hR) hγ)
                  (add_le_add le_rfl (div_le_div_of_nonneg_right (radial_lower R hR) ht))
              _ = _ := by dsimp [γ]; ring
          · have hα' : α < 0 := lt_of_not_ge hα
            have hdep (v : Fin (n+1)) : c 0 v = 0 := by
              by_cases hv : v = 0
              · simpa [hv] using hc.refl 0
              have hvU : ({v} : Finset (Fin (n+1))) ⊆ clients n := by simp [clients, hv]
              have hT := htour {v} hvU
              have hvT := (hT.2 v).mpr (by simp)
              have hle := hctour {v} hvU
              have hnon := tsp_nonneg {v}
              have hmul : α * tspOn c {v} ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hα'.le hnon
              have hvisit := route_visit _ v hvT
              have hcn := hc.nonneg 0 v
              linarith only [hle, hmul, hvisit, hcn]
            have hzero (a b : Fin (n+1)) : c a b = 0 := by
              have ht := hc.triangle a b 0
              have ha := hdep a
              have hb := hdep b
              rw [hc.symm a 0] at ht
              linarith only [ht, ha, hb, hc.nonneg a b]
            have hrzero (L) : SupplyChainTheory.routeCost c L = 0 := by
              have hp (a) (K : List (Fin (n+1))) : path a K = 0 := by
                induction K generalizing a with
                | nil => rw [path_nil, hzero]
                | cons b K ih => rw [path_cons, hzero, ih, zero_add]
              rw [route_path, hp]
            have hszero (R) : SupplyChainTheory.solutionCost c R = 0 := by
              induction R with
              | nil => simp [SupplyChainTheory.solutionCost]
              | cons L R ih => simp only [SupplyChainTheory.solutionCost, List.map_cons, List.sum_cons] at ih ⊢; rw [hrzero, ih, zero_add]
            have hbestzero (U) (hU : U ⊆ clients n) : bestSplit c d (tour U) = 0 := by
              have ht := htour U hU
              have h0 : (0 : Fin (n+1)) ∉ tour U := by
                intro hh
                have := hU ((ht.2 0).mp hh)
                simpa [clients] using this
              obtain ⟨Q, hQ, hcost⟩ := split_attained _ ht.1 h0
              rw [hszero] at hcost
              exact hcost.symm
            have halgzero (S) : alg2Cost c d tour S = 0 := by
              simp [alg2Cost, hrzero, hbestzero _ (show uncovered n S ⊆ clients n from Finset.sdiff_subset)]
            intro R hR
            simp [expect, halgzero, hszero]
