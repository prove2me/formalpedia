-- Prove2me | solution 1 for SparsestCutOracle.Main.sdp_opt_le
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T04:00:58.623993+00:00
-- url     : https://prove2.me/submissions/273c7bd9-2d16-4aea-ac42-8c757e937d12

import Mathlib
import Definitions.Def_SparsestCutOracle_Main_SDP

open scoped BigOperators
open SparsestCutOracle.Main
private def outer {n : ℕ} (x : Fin n → ℝ) : SparsestCutOracle.Main.Mat n := Matrix.of fun i j => x i * x j
private lemma outer_posSemidef {n : ℕ} (x : Fin n → ℝ) : (outer x).PosSemidef := by
  let A : Matrix (Fin 1) (Fin n) ℝ := Matrix.of fun _ i => x i
  have h := Matrix.posSemidef_conjTranspose_mul_self A
  have heq : A.conjTranspose * A = outer x := by
    ext i j
    simp [A, Matrix.mul_apply, outer]
  rwa [heq] at h
private lemma dot_outer {n : ℕ} (A : Mat n) (x : Fin n → ℝ) :
    dot A (outer x) = ∑ i, ∑ j, A i j * x j * x i := by
  unfold dot Matrix.trace Matrix.diag
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mul_apply]
  simp only [outer, Matrix.of_apply, mul_assoc]
private lemma dot_add {n : ℕ} (A B X : Mat n) :
    dot (A + B) X = dot A X + dot B X := by
  simp [dot, Matrix.trace, Matrix.diag, Matrix.mul_apply, add_mul, Finset.sum_add_distrib]
private lemma dot_sub {n : ℕ} (A B X : Mat n) :
    dot (A - B) X = dot A X - dot B X := by
  simp [dot, Matrix.trace, Matrix.diag, Matrix.mul_apply, sub_mul, Finset.sum_sub_distrib]
private lemma dot_smul {n : ℕ} (r : ℝ) (A X : Mat n) :
    dot (r • A) X = r * dot A X := by
  simp [dot, Matrix.trace, Matrix.diag, Matrix.mul_apply, mul_assoc, Finset.mul_sum]
private lemma dot_finset_sum {n : ℕ} {ι : Type*} (s : Finset ι) (A : ι → Mat n) (X : Mat n) :
    dot (∑ i ∈ s, A i) X = ∑ i ∈ s, dot (A i) X := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dot, Matrix.trace, Matrix.diag]
  | @insert a s ha ih => simp only [Finset.sum_insert ha, dot_add, ih]
private lemma dot_edge_outer {n : ℕ} (u v : Fin n) (x : Fin n → ℝ) :
    dot (edgeLaplacian u v) (outer x) = (x u - x v) ^ 2 := by
  rw [dot_outer]
  simp [edgeLaplacian, sub_mul, mul_sub, mul_ite, ite_mul, Finset.sum_sub_distrib]
  ring
private lemma dot_laplacian_outer {n : ℕ} (G : ClusterDecomp.WGraph (Fin n)) (x : Fin n → ℝ) :
    dot (laplacian G) (outer x) = (1 / 2 : ℝ) * ∑ i, ∑ j, G.w i j * (x i - x j) ^ 2 := by
  rw [laplacian, dot_smul, dot_finset_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [dot_finset_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [dot_smul, dot_edge_outer]
private lemma dot_D_outer {n : ℕ} (π x : Fin n → ℝ) :
    dot (D π) (outer x) = ∑ i, π i * x i ^ 2 := by
  rw [dot_outer]
  simp [D, Matrix.diagonal_apply, ite_mul, sq]
  apply Finset.sum_congr rfl
  intro i _
  ring
private lemma dot_J_outer {n : ℕ} (π x : Fin n → ℝ) :
    dot (J π) (outer x) = (∑ i, π i * x i) ^ 2 := by
  rw [dot_outer]
  rw [sq, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [J]
  ring
private lemma cut_double_sum {n : ℕ} (w : Fin n → Fin n → ℝ)
    (hw : ∀ u v, w u v = w v u) (S : Finset (Fin n)) (a c : ℝ)
    (x : Fin n → ℝ) (hx : ∀ i, x i = if i ∈ S then a else c) :
    (∑ i, ∑ j, w i j * (x i - x j) ^ 2) =
      2 * (a - c) ^ 2 * ClusterDecomp.cutCap w S Sᶜ := by
  classical
  have hSS : (∑ i ∈ S, ∑ j ∈ S, w i j * (x i - x j) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    rw [hx i, hx j]
    simp [hi, hj]
  have hTT : (∑ i ∈ Sᶜ, ∑ j ∈ Sᶜ, w i j * (x i - x j) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    rw [hx i, hx j]
    simp only [Finset.mem_compl] at hi hj
    simp [hi, hj]
  have hST : (∑ i ∈ S, ∑ j ∈ Sᶜ, w i j * (x i - x j) ^ 2) =
      ClusterDecomp.cutCap w S Sᶜ * (a - c) ^ 2 := by
    unfold ClusterDecomp.cutCap
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hx i, hx j]
    have hj' : j ∉ S := Finset.mem_compl.mp hj
    simp [hi, hj']
  have hTS : (∑ i ∈ Sᶜ, ∑ j ∈ S, w i j * (x i - x j) ^ 2) =
      ClusterDecomp.cutCap w S Sᶜ * (a - c) ^ 2 := by
    rw [Finset.sum_comm]
    calc
      (∑ j ∈ S, ∑ i ∈ Sᶜ, w i j * (x i - x j) ^ 2) =
          ∑ j ∈ S, ∑ i ∈ Sᶜ, w j i * (x j - x i) ^ 2 := by
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro i _
            rw [hw i j]
            have hs : (x i - x j) ^ 2 = (x j - x i) ^ 2 := by ring
            rw [hs]
      _ = _ := hST
  rw [← Finset.sum_add_sum_compl S (fun i => ∑ j, w i j * (x i - x j) ^ 2)]
  have splitS : (∑ i ∈ S, ∑ j, w i j * (x i - x j) ^ 2) =
      (∑ i ∈ S, ∑ j ∈ S, w i j * (x i - x j) ^ 2) +
        ∑ i ∈ S, ∑ j ∈ Sᶜ, w i j * (x i - x j) ^ 2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact (Finset.sum_add_sum_compl S (fun j => w i j * (x i - x j) ^ 2)).symm
  have splitT : (∑ i ∈ Sᶜ, ∑ j, w i j * (x i - x j) ^ 2) =
      (∑ i ∈ Sᶜ, ∑ j ∈ S, w i j * (x i - x j) ^ 2) +
        ∑ i ∈ Sᶜ, ∑ j ∈ Sᶜ, w i j * (x i - x j) ^ 2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_sum_compl S (fun j => w i j * (x i - x j) ^ 2)]
  rw [splitS, splitT, hSS, hST, hTS, hTT]
  ring
private lemma dot_list_sum {n : ℕ} (l : List (Mat n)) (X : Mat n) :
    dot l.sum X = (l.map fun A => dot A X).sum := by
  induction l with
  | nil => simp [dot, Matrix.trace, Matrix.diag]
  | cons A l ih => simp only [List.sum_cons, List.map_cons, dot_add, ih]
private lemma dot_pathEdges {n : ℕ} (p : List (Fin n)) (x : Fin n → ℝ) :
    dot (pathEdges p) (outer x) =
      ((p.zip p.tail).map fun e => (x e.1 - x e.2) ^ 2).sum := by
  rw [pathEdges, dot_list_sum]
  simp only [List.map_map, Function.comp_def, dot_edge_outer]
private lemma binary_triangle {n : ℕ} (S : Finset (Fin n)) (a c : ℝ)
    (x : Fin n → ℝ) (hx : ∀ i, x i = if i ∈ S then a else c)
    (u v w : Fin n) :
    0 ≤ (x u - x v) ^ 2 + (x v - x w) ^ 2 - (x u - x w) ^ 2 := by
  rw [hx u, hx v, hx w]
  by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> by_cases hw : w ∈ S <;>
    simp only [hu, hv, hw, if_true, if_false] <;> nlinarith [sq_nonneg (a - c)]
private lemma path_dot_binary {n : ℕ} (S : Finset (Fin n)) (a c : ℝ)
    (x : Fin n → ℝ) (hx : ∀ i, x i = if i ∈ S then a else c) :
    ∀ p : List (Fin n), 0 ≤ dot (pathMatrix p) (outer x)
  | [] => by simp [pathMatrix, pathEdges, pathDemand, dot, Matrix.trace, Matrix.diag]
  | [u] => by
      have he : edgeLaplacian u u = (0 : Mat n) := by ext i j; simp [edgeLaplacian]
      simp [pathMatrix, pathEdges, pathDemand, he, dot, Matrix.trace, Matrix.diag]
  | u :: v :: t => by
      have ih := path_dot_binary S a c x hx (v :: t)
      have htr := binary_triangle S a c x hx u v ((v :: t).getLast (by simp))
      have hlast' : (v :: t).getLast? = some ((v :: t).getLast (by simp)) :=
        List.getLast?_eq_some_getLast (by simp)
      have hlast : (u :: v :: t).getLast? = some ((v :: t).getLast (by simp)) := by
        rw [List.getLast?_cons_cons, hlast']
      rw [pathMatrix, dot_sub, dot_pathEdges]
      simp only [List.tail_cons, List.zip_cons_cons, List.map_cons, List.sum_cons]
      rw [pathMatrix, dot_sub, dot_pathEdges] at ih
      simp only [pathDemand, List.head?_cons, hlast, hlast', dot_edge_outer] at *
      simp only [List.tail_cons] at ih
      linarith
private lemma sum_binary {n : ℕ} (π : Fin n → ℝ) (g : ℝ → ℝ) (S : Finset (Fin n))
    (a c : ℝ) (x : Fin n → ℝ) (hx : ∀ i, x i = if i ∈ S then a else c) :
    (∑ i, π i * g (x i)) = mass π S * g a + mass π Sᶜ * g c := by
  rw [← Finset.sum_add_sum_compl S (fun i => π i * g (x i))]
  have hs : (∑ i ∈ S, π i * g (x i)) = mass π S * g a := by
    rw [mass, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hx i]
    simp [hi]
  have ht : (∑ i ∈ Sᶜ, π i * g (x i)) = mass π Sᶜ * g c := by
    rw [mass, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hx i]
    have hi' : i ∉ S := Finset.mem_compl.mp hi
    simp [hi']
  rw [hs, ht]

/-- Lemma 3, p.18: the proof's feasible witness encodes the full optimum bound. -/
theorem solution {n : ℕ} (hn : 2 ≤ n) (cP : ℕ) (hcP : 1 ≤ cP)
    (G : ClusterDecomp.WGraph (Fin n)) (π : Fin n → ℝ) (hπ : ∀ v, 0 < π v) :
    ∃ X : Mat n, SDPFeasible cP π X ∧
      dot (laplacian G) X ≤ 2 * totalWeight π * sparsest G π := by
  classical
  let 𝒜 : Finset (Finset (Fin n)) := Finset.univ.filter fun S => S.Nonempty ∧ S ≠ Finset.univ
  have h𝒜 : 𝒜.Nonempty := by
    let u : Fin n := ⟨0, by omega⟩
    let v : Fin n := ⟨1, by omega⟩
    have huv : u ≠ v := by
      intro h
      have he := congrArg Fin.val h
      simp [u, v] at he
    have hproper : ({u} : Finset (Fin n)) ≠ Finset.univ := by
      intro h
      have hm : v ∈ ({u} : Finset (Fin n)) := by rw [h]; simp
      have hvu : v = u := by simpa using hm
      exact huv hvu.symm
    exact ⟨{u}, by simp [𝒜, hproper]⟩
  obtain ⟨S, hS𝒜, hmin⟩ := Finset.exists_min_image 𝒜 (sparsity G π) h𝒜
  have hSprops : S.Nonempty ∧ S ≠ Finset.univ := by simpa [𝒜] using hS𝒜
  obtain ⟨hSne, hSproper⟩ := hSprops
  let f : {T // T ∈ 𝒜} → ℝ := fun T => sparsity G π T.1
  have hfinite : {r : ℝ | ∃ T : Finset (Fin n),
      T.Nonempty ∧ T ≠ Finset.univ ∧ r = sparsity G π T}.Finite := by
    have heq : {r : ℝ | ∃ T : Finset (Fin n),
        T.Nonempty ∧ T ≠ Finset.univ ∧ r = sparsity G π T} = Set.range f := by
      ext r
      constructor
      · rintro ⟨T, hTne, hTproper, rfl⟩
        exact ⟨⟨T, by simp [𝒜, hTne, hTproper]⟩, rfl⟩
      · rintro ⟨T, rfl⟩
        have hTmem := T.2
        simp only [𝒜, Finset.mem_filter, Finset.mem_univ, true_and] at hTmem
        exact ⟨T.1, hTmem.1, hTmem.2, rfl⟩
    rw [heq]
    exact Set.finite_range f
  have hopt : sparsest G π = sparsity G π S := by
    apply le_antisymm
    · apply csInf_le hfinite.bddBelow
      exact ⟨S, hSne, hSproper, rfl⟩
    · apply le_csInf
      · exact ⟨sparsity G π S, S, hSne, hSproper, rfl⟩
      · intro r hr
        obtain ⟨T, hTne, hTproper, rfl⟩ := hr
        exact hmin T (by simp [𝒜, hTne, hTproper])
  have hSc : Sᶜ.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    apply hSproper
    ext v
    simp only [Finset.mem_univ, iff_true]
    by_contra hv
    have hv' : v ∈ Sᶜ := Finset.mem_compl.mpr hv
    rw [h] at hv'
    simp at hv'
  let a := mass π S
  let b := mass π Sᶜ
  have ha : 0 < a := by
    dsimp [a, mass]
    exact Finset.sum_pos (fun i _ => hπ i) hSne
  have hb : 0 < b := by
    dsimp [b, mass]
    exact Finset.sum_pos (fun i _ => hπ i) hSc
  have hPi : totalWeight π = a + b := by
    dsimp [totalWeight, a, b, mass]
    rw [← Finset.sum_add_sum_compl S π]
  let r := Real.sqrt (a * b)
  have hr : 0 < r := Real.sqrt_pos.2 (mul_pos ha hb)
  have hr2 : r ^ 2 = a * b := Real.sq_sqrt (mul_nonneg ha.le hb.le)
  let x : Fin n → ℝ := fun i => if i ∈ S then b / r else -a / r
  have hx : ∀ i, x i = if i ∈ S then b / r else -a / r := fun _ => rfl
  refine ⟨outer x, ⟨outer_posSemidef x, ?_, ?_, ?_⟩, ?_⟩
  · rw [dot_J_outer, sum_binary π (fun z => z) S (b / r) (-a / r) x hx]
    change (a * (b / r) + b * (-a / r)) ^ 2 = 0
    have hz : a * (b / r) + b * (-a / r) = 0 := by
      field_simp [ne_of_gt hr]
      ring
    rw [hz]
    ring
  · rw [dot_D_outer, sum_binary π (fun z => z ^ 2) S (b / r) (-a / r) x hx, hPi]
    change a * (b / r) ^ 2 + b * (-a / r) ^ 2 = a + b
    field_simp [ne_of_gt hr]
    rw [hr2]
    ring
  · intro p _
    exact path_dot_binary S (b / r) (-a / r) x hx p
  · have hcut : 0 ≤ G.cut S Sᶜ := by
      unfold ClusterDecomp.WGraph.cut ClusterDecomp.cutCap
      apply Finset.sum_nonneg
      intro i _
      apply Finset.sum_nonneg
      intro j _
      exact G.nonneg i j
    rw [hopt, hPi, sparsity, dot_laplacian_outer,
      cut_double_sum G.w G.symm S (b / r) (-a / r) x hx]
    change (1 / 2 : ℝ) * (2 * (b / r - -a / r) ^ 2 * G.cut S Sᶜ) ≤
      2 * (a + b) * (G.cut S Sᶜ / min a b)
    have heq : (1 / 2 : ℝ) * (2 * (b / r - -a / r) ^ 2 * G.cut S Sᶜ) =
        (b / r - -a / r) ^ 2 * G.cut S Sᶜ := by ring
    rw [heq]
    by_cases hab : a ≤ b
    · rw [min_eq_left hab]
      have hfac : 0 ≤ (a + b) * G.cut S Sᶜ / a := by positivity
      calc
        (b / r - -a / r) ^ 2 * G.cut S Sᶜ =
            ((a + b) / b) * ((a + b) * G.cut S Sᶜ / a) := by
          field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hr]
          rw [hr2]
          ring
        _ ≤ 2 * ((a + b) * G.cut S Sᶜ / a) := by
          apply mul_le_mul_of_nonneg_right _ hfac
          apply (div_le_iff₀ hb).2
          linarith
        _ = 2 * (a + b) * (G.cut S Sᶜ / a) := by ring
    · have hab' : b ≤ a := le_of_not_ge hab
      rw [min_eq_right hab']
      have hfac : 0 ≤ (a + b) * G.cut S Sᶜ / b := by positivity
      calc
        (b / r - -a / r) ^ 2 * G.cut S Sᶜ =
            ((a + b) / a) * ((a + b) * G.cut S Sᶜ / b) := by
          field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hr]
          rw [hr2]
          ring
        _ ≤ 2 * ((a + b) * G.cut S Sᶜ / b) := by
          apply mul_le_mul_of_nonneg_right _ hfac
          apply (div_le_iff₀ ha).2
          linarith
        _ = 2 * (a + b) * (G.cut S Sᶜ / b) := by ring
