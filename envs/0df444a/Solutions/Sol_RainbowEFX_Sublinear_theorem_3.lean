-- Prove2me | solution 1 for RainbowEFX.Sublinear.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T07:06:39.943625+00:00
-- url     : https://prove2.me/submissions/7ad96f44-4ffa-4c3e-b957-a2369f6ac2aa

import Mathlib
import Definitions.Def_RainbowEFX_Sublinear_Setting

open LittleCharity.EFX RainbowEFX.Sublinear

theorem REFX_finRotate_val (n : ℕ) (j : Fin n) :
    (finRotate n j).val = if j.val + 1 = n then 0 else j.val + 1 := by
  cases n with
  | zero => exact j.elim0
  | succ n =>
    rw [coe_finRotate]
    by_cases h : j = Fin.last n
    · subst h; simp
    · have : j.val ≠ n := fun h' => h (Fin.ext h')
      rw [if_neg h, if_neg (by omega)]

/-- Theorem 3, main part: more than `d⁴ + d` parts of size between `1` and `d` with the in-edge
property force a cycle visiting each part at most once. -/
theorem REFX_rainbow_main (d : ℕ) (hd : 1 ≤ d) {ι V : Type} [Fintype ι] (part : V → ι)
    (adj : V → V → Prop) (hk : d ^ 4 + d < Fintype.card ι)
    (hparts : ∀ i : ι, 1 ≤ Nat.card {w : V // part w = i} ∧
      Nat.card {w : V // part w = i} ≤ d)
    (hin : InEdgeProperty part adj) :
    ∃ (r : ℕ) (c : Fin r → V), IsRainbowCycle part adj c := by
  classical
  haveI : ∀ i, Finite {w // part w = i} := fun i =>
    Nat.finite_of_card_ne_zero (by have := (hparts i).1; omega)
  haveI : Finite V := Finite.of_equiv _ (Equiv.sigmaFiberEquiv part)
  letI : Fintype V := Fintype.ofFinite V
  -- parts as finsets
  set P : ι → Finset V := fun i => Finset.univ.filter (fun w => part w = i) with hPdef
  have hPcard : ∀ i, (P i).card = Nat.card {w // part w = i} := by
    intro i
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hP1 : ∀ i, 1 ≤ (P i).card := fun i => by rw [hPcard]; exact (hparts i).1
  have hPd : ∀ i, (P i).card ≤ d := fun i => by rw [hPcard]; exact (hparts i).2
  have hmemP : ∀ w i, w ∈ P i ↔ part w = i := by intro w i; simp [hPdef]
  -- choose `d` distinguished parts
  have hdk : d ≤ Fintype.card ι := by
    have : d ≤ d ^ 4 + d := Nat.le_add_left d _
    omega
  set p : Fin d → ι := fun i => (Fintype.equivFin ι).symm (Fin.castLE hdk i) with hpdef
  have hpinj : Function.Injective p := by
    intro i j h
    simpa [hpdef, Fin.castLE_inj] using h
  set L : Finset ι := Finset.univ \ Finset.univ.image p with hLdef
  have hLcard : L.card = Fintype.card ι - d := by
    rw [hLdef, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Finset.card_image_of_injective _ hpinj, Finset.card_univ, Fintype.card_fin]
  have hpL : ∀ i, p i ∉ L := by intro i; simp [hLdef]
  -- the "path through part ℓ" sets
  set S : Fin d → ι → Finset (V × V) := fun i ℓ => Finset.univ.filter (fun e : V × V =>
    part e.1 = p i ∧ (∃ j, part e.2 = p j) ∧ ∃ z, part z = ℓ ∧ adj e.1 z ∧ adj z e.2) with hSdef
  set U : Fin d → Finset (V × V) := fun i =>
    (P (p i)) ×ˢ (Finset.univ.biUnion (fun j => P (p j))) with hUdef
  have hSU : ∀ i ℓ, S i ℓ ⊆ U i := by
    intro i ℓ e he
    simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and] at he
    obtain ⟨h1, ⟨j, hj⟩, -⟩ := he
    simp only [hUdef, Finset.mem_product, Finset.mem_biUnion, Finset.mem_univ, true_and, hmemP]
    exact ⟨h1, j, hj⟩
  have hUcard : ∀ i, (U i).card ≤ d ^ 3 := by
    intro i
    rw [hUdef, Finset.card_product]
    have h1 := hPd (p i)
    have h2 : (Finset.univ.biUnion (fun j => P (p j))).card ≤ d * d := by
      refine (Finset.card_biUnion_le).trans ?_
      calc ∑ j : Fin d, (P (p j)).card ≤ ∑ _j : Fin d, d := Finset.sum_le_sum (fun j _ => hPd _)
        _ = d * d := by simp
    calc (P (p i)).card * (Finset.univ.biUnion (fun j => P (p j))).card ≤ d * (d * d) :=
          Nat.mul_le_mul h1 h2
      _ = d ^ 3 := by ring
  -- Observation 18 (representative sets)
  have hrep : ∀ i (L' : Finset ι), ∃ B, B ⊆ L' ∧ B.card ≤ d ^ 3 ∧
      ∀ ℓ ∈ L', ∀ e ∈ S i ℓ, ∃ ℓ' ∈ B, e ∈ S i ℓ' := by
    intro i L'
    set T := L'.biUnion (S i) with hT
    refine ⟨T.attach.image (fun e => Classical.choose (Finset.mem_biUnion.mp e.2)), ?_, ?_, ?_⟩
    · intro ℓ hℓ
      obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hℓ
      exact (Classical.choose_spec (Finset.mem_biUnion.mp e.2)).1
    · refine Finset.card_image_le.trans ?_
      rw [Finset.card_attach]
      refine (Finset.card_le_card ?_).trans (hUcard i)
      intro e he
      obtain ⟨ℓ, -, he⟩ := Finset.mem_biUnion.mp he
      exact hSU i ℓ he
    · intro ℓ hℓ e he
      have heT : e ∈ T := Finset.mem_biUnion.mpr ⟨ℓ, hℓ, he⟩
      exact ⟨_, Finset.mem_image.mpr ⟨⟨e, heT⟩, Finset.mem_attach _ _, rfl⟩,
        (Classical.choose_spec (Finset.mem_biUnion.mp heT)).2⟩
  -- the sequential construction of pairwise disjoint representative sets
  have hseq : ∀ F : Finset (Fin d), ∀ L' : Finset ι, ∃ W : Fin d → Finset ι,
      (∀ i ∈ F, W i ⊆ L' ∧ (W i).card ≤ d ^ 3) ∧
      (∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (W i) (W j)) ∧
      (∀ i ∈ F, ∀ ℓ ∈ L', (∀ j ∈ F, ℓ ∉ W j) → ∀ e ∈ S i ℓ, ∃ ℓ' ∈ W i, e ∈ S i ℓ') := by
    intro F
    induction F using Finset.induction_on with
    | empty => intro L'; exact ⟨fun _ => ∅, by simp, by simp, by simp⟩
    | insert a F ha ih =>
      intro L'
      obtain ⟨B, hBL, hBc, hBcov⟩ := hrep a L'
      obtain ⟨W, hW1, hW2, hW3⟩ := ih (L' \ B)
      refine ⟨Function.update W a B, ?_, ?_, ?_⟩
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · simpa using ⟨hBL, hBc⟩
        · have hia : i ≠ a := fun h => ha (h ▸ hi)
          rw [Function.update_of_ne hia]
          exact ⟨(hW1 i hi).1.trans Finset.sdiff_subset, (hW1 i hi).2⟩
      · intro i hi j hj hij
        have key : ∀ k ∈ F, Disjoint B (W k) := by
          intro k hk
          rw [Finset.disjoint_left]
          intro x hxB hxW
          have := (hW1 k hk).1 hxW
          exact (Finset.mem_sdiff.mp this).2 hxB
        rcases Finset.mem_insert.mp hi with rfl | hi' <;>
          rcases Finset.mem_insert.mp hj with rfl | hj'
        · exact absurd rfl hij
        · have hja : j ≠ i := fun h => ha (h ▸ hj')
          rw [Function.update_self, Function.update_of_ne hja]
          exact key j hj'
        · have hia : i ≠ j := fun h => ha (h ▸ hi')
          rw [Function.update_self, Function.update_of_ne hia]
          exact (key i hi').symm
        · have hia : i ≠ a := fun h => ha (h ▸ hi')
          have hja : j ≠ a := fun h => ha (h ▸ hj')
          rw [Function.update_of_ne hia, Function.update_of_ne hja]
          exact hW2 i hi' j hj' hij
      · intro i hi ℓ hℓ hnot e he
        rcases Finset.mem_insert.mp hi with rfl | hi'
        · rw [Function.update_self]
          exact hBcov ℓ hℓ e he
        · have hia : i ≠ a := fun h => ha (h ▸ hi')
          rw [Function.update_of_ne hia]
          have hℓB : ℓ ∉ B := by
            have h2 := hnot _ (Finset.mem_insert_self a F)
            simpa using h2
          refine hW3 i hi' ℓ (Finset.mem_sdiff.mpr ⟨hℓ, hℓB⟩) ?_ e he
          intro j hj
          have := hnot j (Finset.mem_insert_of_mem hj)
          have hja : j ≠ a := fun h => ha (h ▸ hj)
          rwa [Function.update_of_ne hja] at this
  obtain ⟨W, hW1, hW2, hW3⟩ := hseq Finset.univ L
  -- a part `ℓ̃ ∈ L` used by none of the representative sets
  have hWall : (Finset.univ.biUnion W).card < L.card := by
    have h1 : (Finset.univ.biUnion W).card ≤ d * d ^ 3 := by
      refine (Finset.card_biUnion_le).trans ?_
      calc ∑ i : Fin d, (W i).card ≤ ∑ _i : Fin d, d ^ 3 :=
            Finset.sum_le_sum (fun i _ => (hW1 i (Finset.mem_univ _)).2)
        _ = d * d ^ 3 := by simp
    rw [hLcard]
    have : d * d ^ 3 = d ^ 4 := by ring
    rw [this] at h1
    omega
  obtain ⟨lt, hltL, hltW⟩ := Finset.exists_mem_notMem_of_card_lt_card hWall
  have hltW' : ∀ j, lt ∉ W j := by
    intro j hj
    exact hltW (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hj⟩)
  -- the backward walk alternating between `ℓ̃` and the distinguished parts
  set q : ℕ → ι := fun k => p ⟨k % d, Nat.mod_lt _ (by omega)⟩ with hqdef
  have hqlt : ∀ k, q k ≠ lt := fun k h => hpL _ (h ▸ hltL)
  set predIn : ι → V → V := fun I w =>
    if h : ∃ u, part u = I ∧ adj u w then Classical.choose h else w with hpredIn
  have hpred : ∀ I w, I ≠ part w → part (predIn I w) = I ∧ adj (predIn I w) w := by
    intro I w hI
    have h := hin w I hI
    simp only [hpredIn, dif_pos h]
    exact Classical.choose_spec h
  obtain ⟨y0, hy0⟩ := Finset.card_pos.mp (hP1 lt)
  set y : ℕ → V := fun k => Nat.rec y0 (fun k yk => predIn lt (predIn (q k) yk)) k with hydef
  set x : ℕ → V := fun k => predIn (q k) (y k) with hxdef
  have hysucc : ∀ k, y (k + 1) = predIn lt (x k) := fun k => rfl
  have hypart : ∀ k, part (y k) = lt := by
    intro k
    induction k with
    | zero => exact (hmemP _ _).mp hy0
    | succ k ih =>
      rw [hysucc]
      have hx := hpred (q k) (y k) (by rw [ih]; exact hqlt k)
      exact (hpred lt (x k) (by rw [hx.1]; exact (hqlt k).symm)).1
  have hxpart : ∀ k, part (x k) = q k ∧ adj (x k) (y k) := fun k =>
    hpred (q k) (y k) (by rw [hypart k]; exact hqlt k)
  have hyx : ∀ k, adj (y (k + 1)) (x k) := by
    intro k
    rw [hysucc]
    exact (hpred lt (x k) (by rw [(hxpart k).1]; exact (hqlt k).symm)).2
  -- pigeonhole on `y 0, …, y d`
  obtain ⟨a', ha', b', hb', hab', hyab'⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (d + 1)) (t := P lt) (f := y)
    (by rw [Finset.card_range]; have := hPd lt; omega)
    (fun k _ => (hmemP _ _).mpr (hypart k))
  obtain ⟨a, b, hab, hbd, hyab⟩ : ∃ a b, a < b ∧ b ≤ d ∧ y a = y b := by
    rw [Finset.mem_range] at ha' hb'
    rcases Nat.lt_or_gt_of_ne hab' with h | h
    · exact ⟨a', b', h, by omega, hyab'⟩
    · exact ⟨b', a', h, by omega, hyab'.symm⟩
  -- successor index on the short cycle `x (b-1) → x (b-2) → ⋯ → x a → x (b-1)`
  set nxt : ℕ → ℕ := fun k => if k = a then b - 1 else k - 1 with hnxt
  -- bypass vertices
  have hbyp : ∀ k, a ≤ k → k < b → ∃ z, part z ∈ W ⟨k % d, Nat.mod_lt _ (by omega)⟩ ∧
      adj (x k) z ∧ adj z (x (nxt k)) := by
    intro k hak hkb
    set i : Fin d := ⟨k % d, Nat.mod_lt _ (by omega)⟩ with hi
    have hmid : adj (y k) (x (nxt k)) := by
      by_cases hka : k = a
      · simp only [hnxt, if_pos hka]
        rw [hka, hyab, show b = (b - 1) + 1 by omega]
        exact hyx _
      · simp only [hnxt, if_neg hka]
        rw [show k = (k - 1) + 1 by omega]
        exact hyx _
    have heS : (x k, x (nxt k)) ∈ S i lt := by
      simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨(hxpart k).1, ⟨⟨(nxt k) % d, Nat.mod_lt _ (by omega)⟩, (hxpart _).1⟩,
        y k, hypart k, (hxpart k).2, hmid⟩
    obtain ⟨ℓ', hℓ'W, hℓ'S⟩ := hW3 i (Finset.mem_univ _) lt hltL
      (fun j _ => hltW' j) _ heS
    simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and] at hℓ'S
    obtain ⟨-, -, z, hz, hz1, hz2⟩ := hℓ'S
    exact ⟨z, hz ▸ hℓ'W, hz1, hz2⟩
  set zz : ℕ → V := fun k =>
    if h : (a ≤ k ∧ k < b) then Classical.choose (hbyp k h.1 h.2) else x k with hzz
  have hzzspec : ∀ k, a ≤ k → k < b →
      part (zz k) ∈ W ⟨k % d, Nat.mod_lt _ (by omega)⟩ ∧ adj (x k) (zz k) ∧
        adj (zz k) (x (nxt k)) := by
    intro k h1 h2
    simp only [hzz, dif_pos (And.intro h1 h2)]
    exact Classical.choose_spec (hbyp k h1 h2)
  -- the rainbow cycle of length `2 (b - a)`
  set N := b - a with hN
  have hN1 : 1 ≤ N := by omega
  set idx : ℕ → ℕ := fun j => b - 1 - j / 2 with hidx
  refine ⟨2 * N, fun j => if j.val % 2 = 0 then x (idx j.val) else zz (idx j.val), ?_, ?_, ?_⟩
  · omega
  · -- each part is visited at most once
    have hidx_range : ∀ j, j < 2 * N → a ≤ idx j ∧ idx j < b := by
      intro j hj; simp only [hidx]; omega
    have hidx_inj : ∀ j j', j < 2 * N → j' < 2 * N → idx j = idx j' → j / 2 = j' / 2 := by
      intro j j' hj hj' h; simp only [hidx] at h; omega
    have hmodd : ∀ k, k < b → k % d = k := fun k hk => Nat.mod_eq_of_lt (by omega)
    intro j j' hjj
    simp only [Function.comp_apply] at hjj
    have hj := j.isLt
    have hj' := j'.isLt
    obtain ⟨hr1, hr2⟩ := hidx_range j hj
    obtain ⟨hr1', hr2'⟩ := hidx_range j' hj'
    apply Fin.ext
    by_cases he : j.val % 2 = 0 <;> by_cases he' : j'.val % 2 = 0 <;>
      simp only [he, he', if_true, if_false] at hjj
    · rw [(hxpart _).1, (hxpart _).1] at hjj
      have := hpinj hjj
      simp only [Fin.mk.injEq, hmodd _ hr2, hmodd _ hr2'] at this
      have := hidx_inj _ _ hj hj' this
      omega
    · exfalso
      rw [(hxpart _).1] at hjj
      have hmem := (hzzspec _ hr1' hr2').1
      rw [← hjj] at hmem
      exact hpL _ ((hW1 _ (Finset.mem_univ _)).1 hmem)
    · exfalso
      rw [(hxpart _).1] at hjj
      have hmem := (hzzspec _ hr1 hr2).1
      rw [hjj] at hmem
      exact hpL _ ((hW1 _ (Finset.mem_univ _)).1 hmem)
    · have hm1 := (hzzspec _ hr1 hr2).1
      have hm2 := (hzzspec _ hr1' hr2').1
      rw [hjj] at hm1
      by_contra hne
      have hidne : idx j.val ≠ idx j'.val := by
        intro h
        have := hidx_inj _ _ hj hj' h
        omega
      have hfne : (⟨idx j.val % d, Nat.mod_lt _ (by omega)⟩ : Fin d) ≠
          ⟨idx j'.val % d, Nat.mod_lt _ (by omega)⟩ := by
        intro h
        simp only [Fin.mk.injEq, hmodd _ hr2, hmodd _ hr2'] at h
        exact hidne h
      exact Finset.disjoint_left.mp (hW2 _ (Finset.mem_univ _) _ (Finset.mem_univ _) hfne)
        hm1 hm2
  · -- consecutive vertices are adjacent
    intro j
    have hj := j.isLt
    have hr : a ≤ idx j.val ∧ idx j.val < b := by simp only [hidx]; omega
    by_cases he : j.val % 2 = 0
    · have hrot : (finRotate (2 * N) j).val = j.val + 1 := by
        rw [REFX_finRotate_val, if_neg (by omega)]
      simp only [he, if_true, hrot, show (j.val + 1) % 2 ≠ 0 by omega, if_false,
        show idx (j.val + 1) = idx j.val by simp only [hidx]; omega]
      exact (hzzspec _ hr.1 hr.2).2.1
    · simp only [he, if_false]
      have h2 := (hzzspec _ hr.1 hr.2).2.2
      by_cases hl : j.val + 1 = 2 * N
      · have hrot : (finRotate (2 * N) j).val = 0 := by
          rw [REFX_finRotate_val, if_pos hl]
        simp only [hrot, Nat.zero_mod, if_true]
        have hia : idx j.val = a := by simp only [hidx]; omega
        rw [hia] at h2
        simp only [hnxt, if_true] at h2
        rw [hia]
        simpa [hidx] using h2
      · have hrot : (finRotate (2 * N) j).val = j.val + 1 := by
          rw [REFX_finRotate_val, if_neg hl]
        simp only [hrot, show (j.val + 1) % 2 = 0 by omega, if_true]
        have hia : idx j.val ≠ a := by simp only [hidx]; omega
        simp only [hnxt, if_neg hia] at h2
        have : idx (j.val + 1) = idx j.val - 1 := by simp only [hidx]; omega
        rw [this]
        exact h2

theorem solution (d : ℕ) (hd : 1 ≤ d) :
    BddAbove {k : ℕ | RainbowFree d k} ∧ rainbowCycleNumber d ≤ d ^ 4 + d ∧
    ∀ {ι V : Type} [Fintype ι] (part : V → ι) (adj : V → V → Prop),
      d ^ 4 + d < Fintype.card ι →
      (∀ i : ι, 1 ≤ Nat.card {w : V // part w = i} ∧ Nat.card {w : V // part w = i} ≤ d) →
      InEdgeProperty part adj →
      ∃ (r : ℕ) (c : Fin r → V), IsRainbowCycle part adj c := by
  have hle : ∀ k, RainbowFree d k → k ≤ d ^ 4 + d := by
    intro k ⟨a, adj, ha, hin, hno⟩
    by_contra hk
    push_neg at hk
    have hcard : ∀ i : Fin k, Nat.card {w : (Σ i, Fin (a i)) // w.1 = i} = a i := by
      intro i
      rw [Nat.card_congr (Equiv.sigmaSubtype i), Nat.card_eq_fintype_card, Fintype.card_fin]
    obtain ⟨r, c, hc⟩ := REFX_rainbow_main d hd (ι := Fin k) Sigma.fst adj
      (by rw [Fintype.card_fin]; exact hk) (fun i => by rw [hcard]; exact ha i) hin
    exact hno r c hc
  refine ⟨⟨d ^ 4 + d, fun k hk => hle k hk⟩, ?_, ?_⟩
  · exact csSup_le' (fun k hk => hle k hk)
  · intro ι V _ part adj hk hparts hin
    exact REFX_rainbow_main d hd part adj hk hparts hin
